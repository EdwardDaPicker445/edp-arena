/*
 * EDP Arena FPS - multiplayer server (no npm packages needed, Node 16+).
 *
 *   node server.js            -> http://localhost:3000   (PORT=8080 node server.js to change)
 *
 * Serves index.html and /sounds/ from this folder, and a WebSocket endpoint at /ws.
 * The server owns HP, kills, deaths, respawns and the match score; clients send their
 * position ~20x/second and report hits (hitscan is decided on the shooter's side).
 */
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = +process.env.PORT || 3000;
const ROOT = __dirname;
const GOAL = 15, MAX_PLAYERS = 8, TICK_MS = 33, RESTART_MS = 10000, PROTECT_MS = 2000, MIN_DEAD_MS = 2000;
const DMG_BODY = 25, DMG_HEAD = 60;
const MAX_MSG = 12 * 1024 * 1024;   // custom maps are sent as one message
const MAX_NET = 256 * 1024;         // largest relayed game packet
const BACKLOG = 32 * 1024;          // if a client has more than this queued, skip stale position data for it
/* Fast-changing relayed packets (positions etc). If a receiver is backlogged these are dropped instead of queued,
   because a late position is worse than a missing one (it causes the rubber-band / teleport).
   Adjust the names to whatever your client puts in d.t when it sends movement. */
const VOLATILE = new Set(['pos', 'state', 'move', 'p', 's', 'snap', 'look', 'anim']);

/* ---------------- static files ---------------- */
const MIME = {'.html':'text/html; charset=utf-8', '.mp3':'audio/mpeg', '.ogg':'audio/ogg', '.wav':'audio/wav',
              '.js':'text/javascript', '.json':'application/json', '.png':'image/png', '.ico':'image/x-icon'};
const server = http.createServer((req, res) => {
  let p = decodeURIComponent((req.url || '/').split('?')[0]);
  if (p === '/') p = '/index.html';
  if (p === '/health') { res.writeHead(200, {'Content-Type': 'text/plain', 'Cache-Control': 'no-store'}); return res.end('ok'); }   // for uptime pingers (keeps Render awake)
  const okPath = p === '/index.html' || p.startsWith('/sounds/');
  const file = path.normalize(path.join(ROOT, p));
  if (!okPath || !file.startsWith(ROOT + path.sep)) { res.writeHead(404); return res.end('Not found'); }
  fs.readFile(file, (err, data) => {
    if (err) { res.writeHead(404); return res.end('Not found'); }
    res.writeHead(200, {'Content-Type': MIME[path.extname(file).toLowerCase()] || 'application/octet-stream',
                        'Cache-Control': 'no-cache'});
    res.end(data);
  });
});

/* ---------------- minimal WebSocket (RFC 6455) ---------------- */
const GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
class Conn {
  constructor(socket) {
    this.socket = socket; this.buf = Buffer.alloc(0); this.pend = []; this.pendLen = 0; this.frag = []; this.fragLen = 0;
    this.open = true; this.onmessage = null; this.onclose = null; this.lastSeen = Date.now();
    socket.on('data', d => this._data(d));
    socket.on('close', () => this._closed());
    socket.on('error', () => { try { socket.destroy(); } catch (e) {} this._closed(); });
    socket.setNoDelay(true);
  }
  _closed() { if (!this.open) return; this.open = false; this.onclose && this.onclose(); }
  _data(d) {
    this.lastSeen = Date.now();   // any frame (incl. the browser's automatic pong) proves the client is still there
    // collect chunks and only concat once enough bytes for the current frame have arrived (avoids O(n^2) copying of big messages)
    this.pend.push(d); this.pendLen += d.length;
    if (this.need && this.pendLen < this.need) return;
    this.need = 0;
    this.buf = this.pend.length > 1 || this.buf.length ? Buffer.concat([this.buf, ...this.pend]) : this.pend[0];
    this.pend = []; this.pendLen = 0;
    for (;;) {
      const b = this.buf;
      if (b.length < 2) return;
      const fin = (b[0] & 0x80) !== 0, op = b[0] & 0x0f, masked = (b[1] & 0x80) !== 0;
      let len = b[1] & 0x7f, off = 2;
      if (len === 126) { if (b.length < 4) return; len = b.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (b.length < 10) return; len = Number(b.readBigUInt64BE(2)); off = 10; }
      if (len > MAX_MSG || !masked) return this.close(1009);
      if (b.length < off + 4 + len) { this.need = off + 4 + len - b.length; this.pendLen = 0; return; }
      const mask = b.subarray(off, off + 4);
      const payload = Buffer.from(b.subarray(off + 4, off + 4 + len));
      for (let i = 0; i < len; i++) payload[i] ^= mask[i & 3];
      this.buf = b.subarray(off + 4 + len);
      if (op === 0x8) return this.close(1000);
      if (op === 0x9) { this._frame(0xA, payload); continue; }
      if (op === 0xA) continue;
      if (op === 0x1 || op === 0x2 || op === 0x0) {
        if (op !== 0x0) { this.frag = []; this.fragLen = 0; }
        this.frag.push(payload); this.fragLen += payload.length;
        if (this.fragLen > MAX_MSG) return this.close(1009);
        if (fin) {
          const msg = Buffer.concat(this.frag).toString('utf8'); this.frag = []; this.fragLen = 0;
          if (this.onmessage) this.onmessage(msg);
        }
      }
    }
  }
  _frame(op, payload) {
    if (!this.open) return;
    const n = payload.length;
    let head;
    if (n < 126) head = Buffer.from([0x80 | op, n]);
    else if (n < 65536) { head = Buffer.alloc(4); head[0] = 0x80 | op; head[1] = 126; head.writeUInt16BE(n, 2); }
    else { head = Buffer.alloc(10); head[0] = 0x80 | op; head[1] = 127; head.writeBigUInt64BE(BigInt(n), 2); }
    try { this.socket.write(Buffer.concat([head, payload])); } catch (e) {}
  }
  send(str) { this._frame(0x1, Buffer.from(str)); }
  get backlog() { return this.socket.writableLength || 0; }
  ping() { this._frame(0x9, Buffer.alloc(0)); }
  terminate() { try { this.socket.destroy(); } catch (e) {} this._closed(); }   // drop a dead connection right away
  close(code) {
    if (!this.open) return;
    const p = Buffer.alloc(2); p.writeUInt16BE(code || 1000, 0);
    this._frame(0x8, p);
    try { this.socket.end(); } catch (e) {}
    this._closed();
  }
}
server.on('upgrade', (req, socket) => {
  const key = req.headers['sec-websocket-key'];
  if (!key || (req.url || '').split('?')[0] !== '/ws') { socket.destroy(); return; }
  const accept = crypto.createHash('sha1').update(key + GUID).digest('base64');
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n' +
               'Sec-WebSocket-Accept: ' + accept + '\r\n\r\n');
  console.log('WebSocket connected from ' + (req.headers['x-forwarded-for'] || socket.remoteAddress));
  onConnection(new Conn(socket));
});

/* ---------------- game rooms ---------------- */
const rooms = new Map();   // name -> {name, players:Map, map:null|object, over:false, timer}
let nextId = 1;
const num = v => (typeof v === 'number' && isFinite(v)) ? v : 0;
const rgb = v => (Number.isInteger(v) && v >= 0 && v <= 0xffffff) ? v : null;   // cosmetic colours chosen in the shop
const clean = (s, n, d) => (String(s == null ? '' : s).replace(/[^\w .\-]/g, '').trim().slice(0, n)) || d;

function getRoom(name) {
  let r = rooms.get(name);
  if (!r) { r = {name, players: new Map(), map: null, mapJson: 'null', over: false, timer: null, hostId: null}; rooms.set(name, r); }
  return r;
}
function bcast(room, obj, except) {
  const s = JSON.stringify(obj);
  for (const p of room.players.values()) if (p !== except && p.conn.open) p.conn.send(s);
}
function pubInfo(p) {
  return {id: p.id, name: p.name, color: p.color, tint: p.tint, tracer: p.tracer, alive: p.alive,
          kills: p.kills, deaths: p.deaths, x: p.x, y: p.y, z: p.z, yaw: p.yaw};
}
function freeColor(room) {
  const used = new Set([...room.players.values()].map(p => p.color));
  for (let i = 0; i < MAX_PLAYERS; i++) if (!used.has(i)) return i;
  return 0;
}
function board(room) {
  return [...room.players.values()].map(p => ({id: p.id, name: p.name, kills: p.kills, deaths: p.deaths}))
    .sort((a, b) => b.kills - a.kills || a.deaths - b.deaths);
}
function resetRoom(room) {
  room.over = false;
  for (const p of room.players.values()) { p.kills = 0; p.deaths = 0; p.hp = 100; p.alive = true; p.protectUntil = Date.now() + PROTECT_MS; }
  bcast(room, {t: 'reset'});
}

function onConnection(conn) {
  let me = null, room = null;
  conn.onmessage = raw => {
    let m; try { m = JSON.parse(raw); } catch (e) { return; }
    if (!m || typeof m.t !== 'string') return;
    const now = Date.now();

    if (m.t === 'join') {
      if (me) return;
      const rname = clean(m.room, 20, 'lobby').toLowerCase();
      room = getRoom(rname);
      if (room.players.size >= MAX_PLAYERS) { conn.send(JSON.stringify({t: 'full'})); return conn.close(1000); }
      if (room.players.size === 0 && m.map && Array.isArray(m.map.assets)) { room.map = m.map; room.mapJson = JSON.stringify(m.map); }   // first player picks the map (serialized once, reused for every join)
      if (room.players.size === 0) { room.over = false; }
      me = {id: nextId++, conn, name: clean(m.name, 16, 'Player'), color: freeColor(room), tint: rgb(m.tint), tracer: rgb(m.tracer),
            x: 0, y: 0, z: 0, yaw: 0, pitch: 0, g: true, hp: 100, alive: true, kills: 0, deaths: 0,
            protectUntil: now + PROTECT_MS, lastHit: 0, deadAt: 0};
      // make names unique
      const names = new Set([...room.players.values()].map(p => p.name));
      if (names.has(me.name)) { let i = 2; while (names.has(me.name + ' ' + i)) i++; me.name += ' ' + i; }
      const others = [...room.players.values()].map(pubInfo);
      room.players.set(me.id, me);
      if (room.hostId === null || !room.players.has(room.hostId)) room.hostId = me.id;   // first player is the room "host"
      const welcome = '{"t":"welcome","id":' + me.id + ',"name":' + JSON.stringify(me.name) + ',"color":' + me.color +
        ',"room":' + JSON.stringify(room.name) + ',"map":' + room.mapJson + ',"goal":' + GOAL +
        ',"players":' + JSON.stringify(others) + ',"over":' + room.over + ',"host":' + (room.hostId === me.id) + '}';
      conn.send(welcome);
      console.log(`[${room.name}] welcome sent to ${me.name}: ${(welcome.length / 1024).toFixed(0)} KB${room.map ? ' (includes the custom map)' : ''}`);
      bcast(room, {t: 'join', p: pubInfo(me)}, me);
      console.log(`[${room.name}] ${me.name} joined (${room.players.size})`);
      return;
    }
    if (!me) return;

    if (m.t === 'net') {   // generic relay: the client game protocol (state/pos/chat/damage/...) passes through untouched
      if (raw.length > MAX_NET || !m.d || typeof m.d !== 'object') return;
      const out = JSON.stringify({t: 'net', from: String(me.id), d: m.d});
      if (m.to != null) {
        const v = room.players.get(Number(m.to));
        if (v && v !== me && v.conn.open) v.conn.send(out);
      } else {
        const vol = VOLATILE.has(m.d.t) || VOLATILE.has(m.d.type);
        for (const p of room.players.values()) {
          if (p === me || !p.conn.open) continue;
          if (vol && p.conn.backlog > BACKLOG) continue;
          p.conn.send(out);
        }
      }
      return;
    }

    if (m.t === 's') {   // position update
      if (!me.alive) return;
      me.hasPos = true;
      me.x = num(m.x); me.y = num(m.y); me.z = num(m.z); me.yaw = num(m.yaw); me.pitch = num(m.pitch); me.g = !!m.g;
    } else if (m.t === 'shot') {
      if (!me.alive || room.over) return;
      bcast(room, {t: 'shot', id: me.id, ex: num(m.ex), ey: num(m.ey), ez: num(m.ez)}, me);
    } else if (m.t === 'hit') {
      const v = room.players.get(m.id);
      if (!v || v === me || !me.alive || !v.alive || room.over) return;
      if (now < v.protectUntil || now - me.lastHit < 60) return;
      me.lastHit = now;
      const head = !!m.head;
      v.hp -= head ? DMG_HEAD : DMG_BODY;
      if (v.hp > 0) { if (v.conn.open) v.conn.send(JSON.stringify({t: 'hp', hp: v.hp, by: me.name})); return; }
      v.hp = 0; v.alive = false; v.deadAt = now; v.deaths++; me.kills++;
      bcast(room, {t: 'kill', killer: me.id, victim: v.id, head, killerName: me.name, victimName: v.name,
                   kills: me.kills, deaths: v.deaths});
      if (me.kills >= GOAL) {
        room.over = true;
        bcast(room, {t: 'end', winner: me.id, winnerName: me.name, board: board(room)});
        clearTimeout(room.timer);
        room.timer = setTimeout(() => { if (rooms.get(room.name) === room) resetRoom(room); }, RESTART_MS);
      }
    } else if (m.t === 'respawn') {
      if (me.alive || now - me.deadAt < MIN_DEAD_MS - 200) return;
      me.alive = true; me.hp = 100; me.protectUntil = now + PROTECT_MS;
      me.x = num(m.x); me.y = num(m.y); me.z = num(m.z);
      conn.send(JSON.stringify({t: 'hp', hp: 100}));
      bcast(room, {t: 'respawn', id: me.id, x: me.x, y: me.y, z: me.z});
    } else if (m.t === 'heal') {
      if (!me.alive || me.hp >= 100) return;
      me.hp = Math.min(100, me.hp + 40);
      conn.send(JSON.stringify({t: 'hp', hp: me.hp}));
    }
  };
  conn.onclose = () => {
    if (!me || !room) return;
    room.players.delete(me.id);
    bcast(room, {t: 'leave', id: me.id, name: me.name});
    if (room.hostId === me.id) {   // host migration: oldest remaining player takes over
      const next = room.players.values().next().value;
      room.hostId = next ? next.id : null;
      if (next) bcast(room, {t: 'host', id: next.id});
    }
    console.log(`[${room.name}] ${me.name} left (${room.players.size})`);
    if (room.players.size === 0) { clearTimeout(room.timer); rooms.delete(room.name); }
    me = null;
  };
}

/* position snapshots to everyone, 20 times a second */
setInterval(() => {
  for (const room of rooms.values()) {
    if (room.players.size < 2) continue;
    const list = [];
    for (const p of room.players.values()) if (p.alive && p.hasPos) list.push([p.id, +p.x.toFixed(2), +p.y.toFixed(2), +p.z.toFixed(2), +p.yaw.toFixed(3), +p.pitch.toFixed(3), p.g ? 1 : 0]);
    if (list.length) {
      const out = JSON.stringify({t: 'snap', ts: Date.now(), p: list});   // ts lets the client interpolate on server time
      for (const p of room.players.values()) if (p.conn.open && p.conn.backlog <= BACKLOG) p.conn.send(out);   // never queue stale snaps
    }
  }
}, TICK_MS);
/* Keep-alive: ping every 15 s; a client that has been silent for 45 s (school Wi-Fi roaming, filter dropping the link, laptop lid shut)
   is removed, so ghost players never keep filling the 8 slots of a room. */
setInterval(() => {
  const now = Date.now();
  for (const room of [...rooms.values()])
    for (const p of [...room.players.values()]) {
      if (now - p.conn.lastSeen > 45000) { console.log(`[${room.name}] ${p.name} timed out`); p.conn.terminate(); }
      else p.conn.ping();
    }
}, 15000);

server.listen(PORT, () => {
  console.log(`EDP Arena FPS server on http://localhost:${PORT}`);
  console.log('Friends on your network can join at http://<your-ip>:' + PORT);
});
