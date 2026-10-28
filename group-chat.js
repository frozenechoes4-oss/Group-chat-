#!/usr/bin/env node
'use strict';

/*
 * ====================================================================
 *  GROUP CHAT  -  server + database + website, all in ONE file
 * ====================================================================
 *  Needs only Node.js 16 or newer. No npm install, no other files.
 *
 *    Start:   node group-chat.js
 *    Open:    http://localhost:3000
 *
 *  Optional settings (environment variables):
 *    PORT=3000            port to listen on
 *    GROUP_NAME="My Gc"   name shown in the app
 *    INVITE_CODE=secret   if set, people need this code to create an account
 *    DATA_DIR=./chat-data where the database and uploads are kept
 *    TRUST_PROXY=1        set when running behind nginx/Cloudflare (HTTPS)
 *
 *  What it does
 *    - Every person creates their own account (username + password).
 *    - The database (chat-data/users.json) keeps each member's name,
 *      username, email, phone, join date, last login and last IP.
 *      Passwords are never stored - only a salted scrypt hash.
 *    - Every message is stored (chat-data/messages.jsonl).
 *    - Photos, voice messages, audio files and videos are stored in
 *      chat-data/media and only logged-in members can open them.
 *    - Links to 18+ sites are rejected by the server.
 *    - The FIRST account created becomes the admin. Admin can see the
 *      member list (Members -> Admin tab), suspend accounts, delete any
 *      message and download all user data as CSV.
 * ====================================================================
 */

const http = require('http');
const fs = require('fs');
const os = require('os');
const path = require('path');
const crypto = require('crypto');
const { Transform, pipeline } = require('stream');

// -------------------------------------------------------------------
//  Settings
// -------------------------------------------------------------------
const PORT = parseInt(process.env.PORT, 10) || 3000;
const HOST = process.env.HOST || '0.0.0.0';
const GROUP_NAME = (process.env.GROUP_NAME || 'Our Group Chat').slice(0, 60);
const INVITE_CODE = process.env.INVITE_CODE || '';
const DATA_DIR = path.resolve(process.env.DATA_DIR || path.join(__dirname, 'chat-data'));
const TRUST_PROXY = process.env.TRUST_PROXY === '1';
const BLOCK_SHORTENERS = true;          // short links (bit.ly...) can hide 18+ sites
const SESSION_DAYS = 30;
const MAX_TEXT = 2000;
const MB = 1024 * 1024;
const LIMITS = { image: 15 * MB, audio: 20 * MB, video: 80 * MB };

const MEDIA_DIR = path.join(DATA_DIR, 'media');
const USERS_FILE = path.join(DATA_DIR, 'users.json');
const SESS_FILE = path.join(DATA_DIR, 'sessions.json');
const MSG_FILE = path.join(DATA_DIR, 'messages.jsonl');

fs.mkdirSync(MEDIA_DIR, { recursive: true });
for (const f of fs.readdirSync(MEDIA_DIR)) {           // clean half-finished uploads
  if (f.startsWith('.tmp-')) { try { fs.unlinkSync(path.join(MEDIA_DIR, f)); } catch (e) {} }
}

// -------------------------------------------------------------------
//  Database (plain files, loaded into memory)
// -------------------------------------------------------------------
function loadJson(file, fallback) {
  try { return JSON.parse(fs.readFileSync(file, 'utf8')); }
  catch (e) { if (e.code === 'ENOENT') return fallback; throw e; }
}
function writeJsonAtomic(file, obj) {
  const tmp = file + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(obj, null, 2));
  fs.renameSync(tmp, file);
}

const usersDb = loadJson(USERS_FILE, { nextId: 1, users: [] });
const usersById = new Map();
const usersByName = new Map();
const usersByEmail = new Map();
function indexUser(u) {
  usersById.set(u.id, u);
  usersByName.set(u.username.toLowerCase(), u);
  usersByEmail.set(u.email.toLowerCase(), u);
}
usersDb.users.forEach(indexUser);
function saveUsers() { writeJsonAtomic(USERS_FILE, usersDb); }

const messages = [];
const msgById = new Map();
let nextMsgId = 1;
if (fs.existsSync(MSG_FILE)) {
  for (const line of fs.readFileSync(MSG_FILE, 'utf8').split('\n')) {
    if (!line.trim()) continue;
    let o;
    try { o = JSON.parse(line); } catch (e) { continue; }
    if (o.t === 'm') {
      const m = Object.assign({}, o); delete m.t;
      messages.push(m); msgById.set(m.id, m);
      if (m.id >= nextMsgId) nextMsgId = m.id + 1;
    } else if (o.t === 'd') {
      const m = msgById.get(o.id);
      if (m) m.deleted = { by: o.by, at: o.at };
    }
  }
}

const sessions = new Map(Object.entries(loadJson(SESS_FILE, {})));
let sessTimer = null;
function saveSessions(now) {
  clearTimeout(sessTimer);
  const go = () => writeJsonAtomic(SESS_FILE, Object.fromEntries(sessions));
  if (now) go(); else sessTimer = setTimeout(go, 300);
}

// -------------------------------------------------------------------
//  Passwords, sessions, small helpers
// -------------------------------------------------------------------
const sha = (s) => crypto.createHash('sha256').update(s).digest('hex');

function hashPw(pw, salt) {
  return new Promise((resolve, reject) => {
    crypto.scrypt(pw, salt, 64, { N: 16384, r: 8, p: 1 }, (e, k) => (e ? reject(e) : resolve(k.toString('hex'))));
  });
}
async function makePw(pw) {
  const salt = crypto.randomBytes(16).toString('hex');
  return { salt, hash: await hashPw(pw, salt) };
}
async function checkPw(u, pw) {
  const h = await hashPw(pw, u.salt);
  return crypto.timingSafeEqual(Buffer.from(h, 'hex'), Buffer.from(u.hash, 'hex'));
}

function parseCookies(req) {
  const out = {};
  String(req.headers.cookie || '').split(';').forEach((p) => {
    const i = p.indexOf('=');
    if (i > 0) { try { out[p.slice(0, i).trim()] = decodeURIComponent(p.slice(i + 1).trim()); } catch (e) {} }
  });
  return out;
}
function newSession(uid) {
  const tok = crypto.randomBytes(32).toString('hex');
  sessions.set(sha(tok), { uid, at: Date.now() });
  saveSessions();
  return tok;
}
function authUser(req) {
  const tok = parseCookies(req).sid;
  if (!tok) return null;
  const key = sha(tok);
  const s = sessions.get(key);
  if (!s) return null;
  if (Date.now() - s.at > SESSION_DAYS * 864e5) { sessions.delete(key); saveSessions(); return null; }
  const u = usersById.get(s.uid);
  if (!u || u.banned) return null;
  return u;
}
function dropSessions(uid) {
  for (const [k, s] of sessions) if (s.uid === uid) sessions.delete(k);
  saveSessions();
}
function cookieHeader(req, tok, maxAge) {
  const https = req.socket.encrypted || (TRUST_PROXY && req.headers['x-forwarded-proto'] === 'https');
  return 'sid=' + tok + '; HttpOnly; SameSite=Strict; Path=/; Max-Age=' + maxAge + (https ? '; Secure' : '');
}
function clientIp(req) {
  if (TRUST_PROXY) {
    const x = req.headers['x-forwarded-for'];
    if (x) return String(x).split(',')[0].trim();
  }
  return String(req.socket.remoteAddress || '').replace(/^::ffff:/, '');
}

const pub = (u) => ({ id: u.id, username: u.username, name: u.name, role: u.role });
const mine = (u) => Object.assign(pub(u), { email: u.email });

// simple in-memory rate limiting
const hits = new Map();
function hitCount(key, win) {
  const now = Date.now();
  const a = (hits.get(key) || []).filter((t) => now - t < win);
  hits.set(key, a);
  return a.length;
}
function addHit(key) { const a = hits.get(key) || []; a.push(Date.now()); hits.set(key, a); }
setInterval(() => { for (const k of hits.keys()) if (!hitCount(k, 3600e3)) hits.delete(k); }, 10 * 60e3).unref();
setInterval(() => {
  const now = Date.now(); let ch = false;
  for (const [k, s] of sessions) if (now - s.at > SESSION_DAYS * 864e5) { sessions.delete(k); ch = true; }
  if (ch) saveSessions();
}, 3600e3).unref();

function flooding(uid) {
  const k = 'msg:' + uid;
  addHit(k);
  return hitCount(k, 10000) > 10;
}

// -------------------------------------------------------------------
//  18+ link filter
// -------------------------------------------------------------------
const ADULT_DOMAINS = [
  'pornhub.com', 'xvideos.com', 'xnxx.com', 'xhamster.com', 'redtube.com', 'youporn.com',
  'spankbang.com', 'brazzers.com', 'onlyfans.com', 'chaturbate.com', 'stripchat.com',
  'livejasmin.com', 'bongacams.com', 'rule34.xxx', 'nhentai.net', 'e-hentai.org', 'hanime.tv',
  'motherless.com', 'eporner.com', 'tnaflix.com', 'tube8.com', 'beeg.com', 'fapello.com',
  'fansly.com', 'camsoda.com', 'myfreecams.com', 'cam4.com', 'erome.com', 'thothub.to',
  'hqporner.com', 'txxx.com', 'hclips.com', 'tubegalore.com', 'daftsex.com', 'sxyprn.com',
  'gelbooru.com', 'e621.net', 'literotica.com', 'fetlife.com', 'ashleymadison.com',
  'adultfriendfinder.com', 'nudevista.com', 'xtube.com', 'drtuber.com', 'vporn.com', '4tube.com',
  'javhd.com', 'missav.com', 'jable.tv', 'hitomi.la', 'tsumino.com', 'fakku.net', 'f95zone.to',
  'rule34.paheal.net', 'ixxx.com', 'tiava.com', 'xxnx.com', 'xvv1deos.com'
];
const ADULT_KEYWORDS = [        // found anywhere inside the host name
  'porn', 'xvideo', 'xnxx', 'xhamster', 'redtube', 'youporn', 'spankbang', 'brazzers',
  'onlyfans', 'chaturbate', 'stripchat', 'livejasmin', 'bongacams', 'rule34', 'hentai',
  'nsfw', 'fansly', 'camsoda', 'myfreecams', 'nudevista', 'thothub', 'fapello', 'cumshot'
];
const ADULT_TOKENS = new Set([  // whole words in the host name (so "essex" is fine)
  'sex', 'sexy', 'xxx', 'porn', 'porno', 'pornos', 'nude', 'nudes', 'erotic', 'erotica',
  'hentai', 'nsfw', 'milf', 'fetish', 'bdsm', 'camgirl', 'camgirls'
]);
const ADULT_TLDS = new Set(['xxx', 'porn', 'sex', 'adult']);
const PATH_KEYWORDS = ['porn', 'hentai', 'nsfw', 'onlyfans', 'rule34', 'nudes'];
const SHORTENERS = [
  'bit.ly', 'tinyurl.com', 't.co', 'goo.gl', 'ow.ly', 'is.gd', 'buff.ly', 'cutt.ly', 'rebrand.ly',
  'shorturl.at', 'tiny.cc', 'rb.gy', 't.ly', 'lnkd.in', 'bl.ink', 'v.gd', 'x.co', 'adf.ly', 'shorte.st'
];
const URL_RE = /(?:[a-z][a-z0-9+.-]*:\/\/|www\.)[^\s<>"'`]+|(?:[a-z0-9](?:[a-z0-9-]*[a-z0-9])?\.)+[a-z]{2,24}(?::\d+)?(?:\/[^\s<>"'`]*)?/g;

function normalizeForLinks(text) {
  let t = String(text).normalize('NFKC').toLowerCase();
  t = t.replace(/[\u200b-\u200f\u2060\ufeff\u00ad]/g, '');
  t = t.replace(/[\u3002\uff0e]/g, '.');
  t = t.replace(/[(\[{]\s*(?:\.|dot)\s*[)\]}]/g, '.');
  t = t.replace(/\bhxxp/g, 'http');
  return t;
}
function hostOf(raw) {
  const x = raw.replace(/^[a-z][a-z0-9+.-]*:\/\//, '');
  const cut = x.search(/[\/?#]/);
  const authority = cut < 0 ? x : x.slice(0, cut);
  const rest = cut < 0 ? '' : x.slice(cut);
  const host = authority.replace(/^.*@/, '').replace(/:\d*$/, '').replace(/\.+$/, '').replace(/^www\d*\./, '');
  return { host, rest };
}
function isAdultHost(host) {
  for (const d of ADULT_DOMAINS) if (host === d || host.endsWith('.' + d)) return true;
  for (const k of ADULT_KEYWORDS) if (host.includes(k)) return true;
  const parts = host.split(/[.\-_]/);
  if (ADULT_TLDS.has(parts[parts.length - 1])) return true;
  return parts.some((p) => ADULT_TOKENS.has(p));
}
function isAdultPath(rest) {
  if (!rest) return false;
  if (PATH_KEYWORDS.some((k) => rest.includes(k))) return true;
  return rest.split(/[^a-z0-9]+/).includes('xxx');
}
function checkText(text) {
  if (!text) return { ok: true };
  const t = normalizeForLinks(text);
  const found = t.match(URL_RE) || [];
  for (const raw of found) {
    const hadScheme = /^[a-z][a-z0-9+.-]*:\/\//.test(raw);
    const { host, rest } = hostOf(raw);
    if (!host) continue;
    if (hadScheme && /^\d{1,3}(\.\d{1,3}){3}$/.test(host)) {
      return { ok: false, error: 'Links to raw IP addresses are not allowed in this group.' };
    }
    if (isAdultHost(host) || isAdultPath(rest)) {
      return { ok: false, error: 'Not sent: 18+ links are banned in this group.' };
    }
    if (BLOCK_SHORTENERS && SHORTENERS.some((d) => host === d || host.endsWith('.' + d))) {
      return { ok: false, error: 'Not sent: shortened links are not allowed because they can hide 18+ sites.' };
    }
  }
  return { ok: true };
}

// -------------------------------------------------------------------
//  Messages and live updates
// -------------------------------------------------------------------
function addMessage(u, type, text, media) {
  const m = { id: nextMsgId++, ts: Date.now(), uid: u.id, type, text: text || '', media: media || null };
  messages.push(m);
  msgById.set(m.id, m);
  fs.appendFileSync(MSG_FILE, JSON.stringify(Object.assign({ t: 'm' }, m)) + '\n');
  return m;
}
function viewMsg(m) {
  const u = usersById.get(m.uid) || { username: 'unknown', name: 'Unknown' };
  const base = { id: m.id, ts: m.ts, uid: m.uid, username: u.username, name: u.name };
  if (m.deleted) return Object.assign(base, { type: 'deleted' });
  const v = Object.assign(base, { type: m.type, text: m.text });
  if (m.media) {
    v.media = { url: '/media/' + m.media.file, mime: m.media.mime, size: m.media.size, name: m.media.name, dur: m.media.dur, voice: !!m.media.voice };
  }
  return v;
}

const clients = new Set();
function broadcast(ev, data) {
  const payload = 'event: ' + ev + '\ndata: ' + JSON.stringify(data) + '\n\n';
  for (const c of clients) { try { c.res.write(payload); } catch (e) {} }
}
const onlineIds = () => Array.from(new Set(Array.from(clients).map((c) => c.uid)));
function kick(uid) {
  for (const c of Array.from(clients)) {
    if (c.uid === uid) {
      try { c.res.write('event: kicked\ndata: {}\n\n'); c.res.end(); } catch (e) {}
      clients.delete(c);
    }
  }
  broadcast('presence', { online: onlineIds() });
}
setInterval(() => { for (const c of clients) { try { c.res.write(': ping\n\n'); } catch (e) {} } }, 25000).unref();

// -------------------------------------------------------------------
//  HTTP helpers
// -------------------------------------------------------------------
function send(res, status, obj, extra) {
  const body = Buffer.from(JSON.stringify(obj));
  res.writeHead(status, Object.assign({
    'Content-Type': 'application/json; charset=utf-8',
    'Content-Length': body.length,
    'Cache-Control': 'no-store'
  }, extra || {}));
  res.end(body);
}
const fail = (res, status, msg) => send(res, status, { error: msg });

function readBody(req, max) {
  return new Promise((resolve, reject) => {
    let size = 0; const chunks = [];
    req.on('data', (c) => {
      size += c.length;
      if (size > max) { reject(Object.assign(new Error('Request too large'), { status: 413 })); req.destroy(); return; }
      chunks.push(c);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
async function readJsonBody(req) {
  const b = await readBody(req, 100 * 1024);
  try { return JSON.parse(b.toString('utf8') || '{}'); }
  catch (e) { throw Object.assign(new Error('Bad request'), { status: 400 }); }
}

// -------------------------------------------------------------------
//  Media
// -------------------------------------------------------------------
const EXT_MIME = {
  jpg: 'image/jpeg', png: 'image/png', gif: 'image/gif', webp: 'image/webp', avif: 'image/avif',
  mp3: 'audio/mpeg', ogg: 'audio/ogg', wav: 'audio/wav', weba: 'audio/webm', m4a: 'audio/mp4', flac: 'audio/flac',
  mp4: 'video/mp4', mov: 'video/quicktime', webm: 'video/webm', ogv: 'video/ogg'
};
function sniff(h, kind) {
  if (h.length < 12) return null;
  const s4 = h.toString('latin1', 0, 4);
  const ftyp = h.toString('latin1', 4, 8) === 'ftyp';
  const brand = h.toString('latin1', 8, 12);
  const ebml = h[0] === 0x1a && h[1] === 0x45 && h[2] === 0xdf && h[3] === 0xa3;
  if (kind === 'image') {
    if (h[0] === 0xff && h[1] === 0xd8 && h[2] === 0xff) return { mime: 'image/jpeg', ext: 'jpg' };
    if (h.slice(0, 8).equals(Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]))) return { mime: 'image/png', ext: 'png' };
    if (s4 === 'GIF8') return { mime: 'image/gif', ext: 'gif' };
    if (s4 === 'RIFF' && brand === 'WEBP') return { mime: 'image/webp', ext: 'webp' };
    if (ftyp && (brand === 'avif' || brand === 'avis')) return { mime: 'image/avif', ext: 'avif' };
    return null;
  }
  if (kind === 'audio') {
    if (s4 === 'OggS') return { mime: 'audio/ogg', ext: 'ogg' };
    if (s4.slice(0, 3) === 'ID3' || (h[0] === 0xff && (h[1] & 0xe0) === 0xe0)) return { mime: 'audio/mpeg', ext: 'mp3' };
    if (s4 === 'RIFF' && brand === 'WAVE') return { mime: 'audio/wav', ext: 'wav' };
    if (s4 === 'fLaC') return { mime: 'audio/flac', ext: 'flac' };
    if (ebml) return { mime: 'audio/webm', ext: 'weba' };
    if (ftyp) return { mime: 'audio/mp4', ext: 'm4a' };
    return null;
  }
  if (kind === 'video') {
    if (ftyp) return brand === 'qt  ' ? { mime: 'video/quicktime', ext: 'mov' } : { mime: 'video/mp4', ext: 'mp4' };
    if (ebml) return { mime: 'video/webm', ext: 'webm' };
    if (s4 === 'OggS') return { mime: 'video/ogg', ext: 'ogv' };
    return null;
  }
  return null;
}

function serveMedia(req, res, p) {
  if (!authUser(req)) return fail(res, 401, 'Please sign in.');
  const name = p.slice(7);
  if (!/^[a-f0-9]{24}\.[a-z0-9]{2,5}$/.test(name)) return fail(res, 404, 'Not found');
  const mime = EXT_MIME[name.split('.')[1]];
  if (!mime) return fail(res, 404, 'Not found');
  const file = path.join(MEDIA_DIR, name);
  fs.stat(file, (err, st) => {
    if (err || !st.isFile()) return fail(res, 404, 'Not found');
    const size = st.size;
    let start = 0, end = size - 1, status = 200;
    const headers = {
      'Content-Type': mime, 'Accept-Ranges': 'bytes', 'Cache-Control': 'private, max-age=86400',
      'X-Content-Type-Options': 'nosniff', 'Content-Security-Policy': "default-src 'none'; sandbox"
    };
    const rg = req.headers.range;
    if (rg) {
      const m = /^bytes=(\d*)-(\d*)$/.exec(rg);
      if (m && (m[1] !== '' || m[2] !== '')) {
        if (m[1] === '') start = Math.max(0, size - parseInt(m[2], 10));
        else { start = parseInt(m[1], 10); if (m[2] !== '') end = Math.min(end, parseInt(m[2], 10)); }
        if (start > end || start >= size) { res.writeHead(416, { 'Content-Range': 'bytes */' + size }); return res.end(); }
        status = 206;
        headers['Content-Range'] = 'bytes ' + start + '-' + end + '/' + size;
      }
    }
    headers['Content-Length'] = end - start + 1;
    res.writeHead(status, headers);
    if (req.method === 'HEAD') return res.end();
    const rs = fs.createReadStream(file, { start, end });
    rs.on('error', () => res.destroy());
    rs.pipe(res);
  });
}

function strike(res, u, chk) {
  u.strikes = (u.strikes || 0) + 1;
  saveUsers();
  return fail(res, 422, chk.error);
}

function handleUpload(req, res, u, url) {
  const kind = url.searchParams.get('kind');
  const limit = LIMITS[kind];
  if (!limit) return fail(res, 400, 'Unsupported file type.');
  const len = parseInt(req.headers['content-length'] || '0', 10);
  if (len > limit) { res.setHeader('Connection', 'close'); return fail(res, 413, 'File too large (max ' + Math.round(limit / MB) + ' MB).'); }
  if (flooding(u.id)) return fail(res, 429, 'You are sending too fast. Please wait a moment.');

  const caption = String(url.searchParams.get('caption') || '').trim().slice(0, 500);
  const name = String(url.searchParams.get('name') || 'file').replace(/[\x00-\x1f\\\/<>:"|?*]+/g, '_').slice(0, 80);
  const dur = Math.max(0, Math.min(parseFloat(url.searchParams.get('dur')) || 0, 3600));
  const voice = kind === 'audio' && url.searchParams.get('voice') === '1';
  const chk = checkText(caption + ' ' + name);
  if (!chk.ok) return strike(res, u, chk);

  const id = crypto.randomBytes(12).toString('hex');
  const tmp = path.join(MEDIA_DIR, '.tmp-' + id);
  let size = 0, head = Buffer.alloc(0), tooBig = false;
  const counter = new Transform({
    transform(chunk, _enc, cb) {
      size += chunk.length;
      if (size > limit) { tooBig = true; return cb(new Error('too big')); }
      if (head.length < 32) head = Buffer.concat([head, chunk.subarray(0, 32 - head.length)]);
      cb(null, chunk);
    }
  });
  pipeline(req, counter, fs.createWriteStream(tmp), (err) => {
    const reply = (status, msg) => { try { if (!res.headersSent) { res.setHeader('Connection', 'close'); fail(res, status, msg); } } catch (e) {} };
    if (err) { fs.unlink(tmp, () => {}); return reply(tooBig ? 413 : 400, tooBig ? 'File too large.' : 'Upload failed.'); }
    const t = size > 0 ? sniff(head, kind) : null;
    if (!t) { fs.unlink(tmp, () => {}); return reply(415, 'That file type is not supported.'); }
    const file = id + '.' + t.ext;
    fs.rename(tmp, path.join(MEDIA_DIR, file), (e2) => {
      if (e2) { fs.unlink(tmp, () => {}); return reply(500, 'Could not save the file.'); }
      const m = addMessage(u, kind, caption, { file, mime: t.mime, size, name, dur, voice });
      const v = viewMsg(m);
      broadcast('msg', v);
      send(res, 200, v);
    });
  });
}

// -------------------------------------------------------------------
//  API
// -------------------------------------------------------------------
async function register(req, res) {
  const ip = clientIp(req);
  if (hitCount('reg:' + ip, 3600e3) >= 10) return fail(res, 429, 'Too many sign-ups from this connection. Try again later.');
  addHit('reg:' + ip);
  const b = await readJsonBody(req);
  if (INVITE_CODE && String(b.invite || '').trim() !== INVITE_CODE) return fail(res, 403, 'Wrong invite code.');
  const username = String(b.username || '').trim();
  const name = String(b.name || '').replace(/\s+/g, ' ').trim();
  const email = String(b.email || '').trim().toLowerCase();
  const phone = String(b.phone || '').trim();
  const pw = String(b.password || '');
  if (name.length < 2 || name.length > 40) return fail(res, 400, 'Please enter your full name (2-40 characters).');
  if (!/^[A-Za-z0-9_.]{3,20}$/.test(username)) return fail(res, 400, 'Username must be 3-20 characters: letters, numbers, dot or underscore.');
  if (email.length > 120 || !/^[^\s@]+@[^\s@]+\.[^\s@]{2,}$/.test(email)) return fail(res, 400, 'Please enter a valid email address.');
  if (phone && !/^[+0-9()\s-]{6,20}$/.test(phone)) return fail(res, 400, 'Phone number looks invalid.');
  if (pw.length < 6 || pw.length > 100) return fail(res, 400, 'Password must be 6-100 characters.');
  if (!checkText(name + ' ' + username).ok || isAdultHost(username.toLowerCase())) return fail(res, 400, 'Please choose a different name or username.');
  if (usersByName.has(username.toLowerCase())) return fail(res, 409, 'That username is already taken.');
  if (usersByEmail.has(email)) return fail(res, 409, 'An account with that email already exists.');

  const { salt, hash } = await makePw(pw);
  if (usersByName.has(username.toLowerCase()) || usersByEmail.has(email)) return fail(res, 409, 'That username or email is already taken.');
  const now = Date.now();
  const u = {
    id: usersDb.nextId++, username, name, email, phone, salt, hash,
    role: usersDb.users.length === 0 ? 'admin' : 'member',
    joinedAt: now, lastLoginAt: now, lastIp: ip,
    ua: String(req.headers['user-agent'] || '').slice(0, 200),
    strikes: 0, banned: false
  };
  usersDb.users.push(u);
  indexUser(u);
  saveUsers();
  const tok = newSession(u.id);
  broadcast('member', { id: u.id });
  send(res, 200, mine(u), { 'Set-Cookie': cookieHeader(req, tok, SESSION_DAYS * 86400) });
}

async function login(req, res) {
  const ip = clientIp(req);
  const b = await readJsonBody(req);
  const id = String(b.username || '').trim().toLowerCase();
  const pw = String(b.password || '');
  const key = 'login:' + ip + ':' + id;
  if (hitCount(key, 15 * 60e3) >= 8) return fail(res, 429, 'Too many failed attempts. Please wait 15 minutes.');
  const u = usersByName.get(id) || usersByEmail.get(id);
  let ok = false;
  if (u) ok = await checkPw(u, pw);
  else await hashPw(pw, '00000000000000000000000000000000');
  if (!ok) { addHit(key); return fail(res, 401, 'Wrong username or password.'); }
  if (u.banned) return fail(res, 403, 'This account has been suspended by the admin.');
  hits.delete(key);
  u.lastLoginAt = Date.now();
  u.lastIp = ip;
  u.ua = String(req.headers['user-agent'] || '').slice(0, 200);
  saveUsers();
  const tok = newSession(u.id);
  send(res, 200, mine(u), { 'Set-Cookie': cookieHeader(req, tok, SESSION_DAYS * 86400) });
}

const csvCell = (v) => {
  let s = String(v == null ? '' : v);
  if (/^[=+\-@\t\r]/.test(s)) s = "'" + s;
  return '"' + s.replace(/"/g, '""') + '"';
};
const iso = (t) => (t ? new Date(t).toISOString() : '');

function adminUsers() {
  const counts = new Map();
  for (const m of messages) counts.set(m.uid, (counts.get(m.uid) || 0) + 1);
  const on = new Set(onlineIds());
  return usersDb.users.map((u) => ({
    id: u.id, username: u.username, name: u.name, email: u.email, phone: u.phone, role: u.role,
    joinedAt: u.joinedAt, lastLoginAt: u.lastLoginAt, lastIp: u.lastIp, strikes: u.strikes || 0,
    banned: !!u.banned, messages: counts.get(u.id) || 0, online: on.has(u.id)
  }));
}

async function api(req, res, url) {
  const p = url.pathname;
  const method = req.method;
  if (method === 'POST' && req.headers['x-chat'] !== '1') return fail(res, 403, 'Forbidden');
  const key = method + ' ' + p;

  if (key === 'GET /api/config') {
    return send(res, 200, {
      group: GROUP_NAME, inviteRequired: !!INVITE_CODE, first: usersDb.users.length === 0,
      limits: LIMITS, maxText: MAX_TEXT
    });
  }
  if (key === 'POST /api/register') return register(req, res);
  if (key === 'POST /api/login') return login(req, res);
  if (key === 'POST /api/logout') {
    const tok = parseCookies(req).sid;
    if (tok) { sessions.delete(sha(tok)); saveSessions(); }
    return send(res, 200, { ok: true }, { 'Set-Cookie': cookieHeader(req, '', 0) });
  }

  const u = authUser(req);
  if (!u) return fail(res, 401, 'Please sign in.');
  if (p.startsWith('/api/admin/') && u.role !== 'admin') return fail(res, 403, 'Admins only.');

  switch (key) {
    case 'GET /api/me':
      return send(res, 200, mine(u));

    case 'GET /api/members': {
      const members = usersDb.users.filter((x) => !x.banned).map((x) => Object.assign(pub(x), { joinedAt: x.joinedAt }));
      return send(res, 200, { members, online: onlineIds() });
    }

    case 'GET /api/messages': {
      const q = url.searchParams;
      const limit = Math.max(1, Math.min(parseInt(q.get('limit'), 10) || 60, 100));
      const before = parseInt(q.get('before'), 10) || 0;
      const after = parseInt(q.get('after'), 10) || 0;
      if (after) {
        const list = messages.filter((m) => m.id > after).slice(0, 200);
        return send(res, 200, { messages: list.map(viewMsg), hasMore: false });
      }
      const pool = before ? messages.filter((m) => m.id < before) : messages;
      const list = pool.slice(-limit);
      return send(res, 200, { messages: list.map(viewMsg), hasMore: pool.length > list.length });
    }

    case 'GET /api/stream': {
      req.socket.setTimeout(0);
      res.writeHead(200, {
        'Content-Type': 'text/event-stream', 'Cache-Control': 'no-cache, no-transform',
        Connection: 'keep-alive', 'X-Accel-Buffering': 'no'
      });
      res.write('retry: 3000\n\n');
      const c = { res, uid: u.id };
      clients.add(c);
      broadcast('presence', { online: onlineIds() });
      req.on('close', () => { clients.delete(c); broadcast('presence', { online: onlineIds() }); });
      return;
    }

    case 'POST /api/check': {
      const b = await readJsonBody(req);
      const chk = checkText(String(b.text || '').slice(0, MAX_TEXT));
      if (!chk.ok) return strike(res, u, chk);
      return send(res, 200, { ok: true });
    }

    case 'POST /api/send': {
      const b = await readJsonBody(req);
      const text = String(b.text || '').replace(/\r\n/g, '\n').trim();
      if (!text) return fail(res, 400, 'Message is empty.');
      if (text.length > MAX_TEXT) return fail(res, 400, 'Message is too long (max ' + MAX_TEXT + ' characters).');
      if (flooding(u.id)) return fail(res, 429, 'You are sending too fast. Please wait a moment.');
      const chk = checkText(text);
      if (!chk.ok) return strike(res, u, chk);
      const m = addMessage(u, 'text', text, null);
      const v = viewMsg(m);
      broadcast('msg', v);
      return send(res, 200, v);
    }

    case 'POST /api/upload':
      return handleUpload(req, res, u, url);

    case 'POST /api/delete': {
      const b = await readJsonBody(req);
      const m = msgById.get(parseInt(b.id, 10));
      if (!m) return fail(res, 404, 'Message not found.');
      if (m.uid !== u.id && u.role !== 'admin') return fail(res, 403, 'You can only delete your own messages.');
      if (!m.deleted) {
        m.deleted = { by: u.id, at: Date.now() };
        fs.appendFileSync(MSG_FILE, JSON.stringify({ t: 'd', id: m.id, by: u.id, at: m.deleted.at }) + '\n');
        broadcast('del', { id: m.id });
      }
      return send(res, 200, { ok: true });
    }

    case 'GET /api/admin/users':
      return send(res, 200, { users: adminUsers(), totalMessages: messages.length });

    case 'GET /api/admin/users.csv': {
      const head = ['id', 'username', 'name', 'email', 'phone', 'role', 'joined', 'last_login', 'last_ip', 'messages', 'blocked_link_attempts', 'status'];
      const rows = adminUsers().map((x) => [x.id, x.username, x.name, x.email, x.phone, x.role, iso(x.joinedAt), iso(x.lastLoginAt), x.lastIp, x.messages, x.strikes, x.banned ? 'suspended' : 'active']);
      const csv = '\ufeff' + [head].concat(rows).map((r) => r.map(csvCell).join(',')).join('\r\n') + '\r\n';
      res.writeHead(200, { 'Content-Type': 'text/csv; charset=utf-8', 'Content-Disposition': 'attachment; filename="chat-users.csv"', 'Cache-Control': 'no-store' });
      return res.end(csv);
    }

    case 'POST /api/admin/ban': {
      const b = await readJsonBody(req);
      const t = usersById.get(parseInt(b.id, 10));
      if (!t) return fail(res, 404, 'User not found.');
      if (t.id === u.id) return fail(res, 400, 'You cannot suspend yourself.');
      if (t.role === 'admin') return fail(res, 400, 'Admins cannot be suspended.');
      t.banned = !!b.banned;
      saveUsers();
      if (t.banned) { dropSessions(t.id); kick(t.id); }
      broadcast('member', { id: t.id });
      return send(res, 200, { ok: true });
    }
  }
  return fail(res, 404, 'Not found');
}

// -------------------------------------------------------------------
//  Server
// -------------------------------------------------------------------
const PAGE_BUF = Buffer.from(String.raw`<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="color-scheme" content="light dark">
<title>Group Chat</title>
<link rel="icon" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 100 100'%3E%3Ctext y='.9em' font-size='90'%3E%F0%9F%92%AC%3C/text%3E%3C/svg%3E">
<style>
:root{--bg:#eaeef3;--panel:#ffffff;--text:#1b2430;--muted:#6a7687;--line:#dde3ea;--accent:#2f6fed;--accent-d:#1f55c4;--me:#d8e6ff;--other:#ffffff;--danger:#d93a3a;--ok:#22a06b;--shadow:0 1px 3px rgba(20,30,50,.12);color-scheme:light dark}
@media (prefers-color-scheme:dark){:root{--bg:#0e131a;--panel:#171e28;--text:#e7ecf3;--muted:#8b97a9;--line:#263041;--accent:#5b8cff;--accent-d:#7aa0ff;--me:#1d3866;--other:#1f2835;--shadow:0 1px 3px rgba(0,0,0,.45)}}
*{box-sizing:border-box}
[hidden]{display:none!important}
html,body{height:100%;margin:0}
body{font-family:system-ui,-apple-system,"Segoe UI",Roboto,"Noto Sans","Noto Sans Bengali",sans-serif;background:var(--bg);color:var(--text);font-size:15px;-webkit-text-size-adjust:100%}
button{font:inherit;color:inherit;cursor:pointer}
input,textarea{font:inherit;color:var(--text)}

/* ---------- sign in / create account ---------- */
.auth{min-height:100%;display:grid;place-items:center;padding:20px;background:linear-gradient(135deg,#2f6fed 0%,#7a4bd8 100%)}
.card{width:100%;max-width:400px;background:var(--panel);border-radius:18px;padding:26px 22px;box-shadow:0 20px 50px rgba(0,0,0,.25)}
.logo{font-size:42px;text-align:center}
.card h1{margin:4px 0 2px;text-align:center;font-size:22px}
.sub{margin:0 0 14px;text-align:center;color:var(--muted)}
.tabs{display:flex;background:var(--bg);border-radius:12px;padding:4px;margin-bottom:12px}
.tabs button{flex:1;border:0;background:none;padding:9px;border-radius:9px;font-weight:600;color:var(--muted)}
.tabs button.on{background:var(--panel);color:var(--text);box-shadow:var(--shadow)}
.card label{display:block;font-size:13px;font-weight:600;color:var(--muted);margin-top:10px}
.card input{display:block;width:100%;margin-top:4px;padding:11px 12px;border:1px solid var(--line);border-radius:10px;background:var(--bg);font-size:16px;outline:none}
.card input:focus{border-color:var(--accent)}
.regonly{display:none}
body[data-mode=reg] .regonly{display:block}
.err{color:var(--danger);font-size:13.5px;min-height:18px;margin:10px 0 0}
.primary{width:100%;margin-top:8px;border:0;background:var(--accent);color:#fff;padding:12px;border-radius:10px;font-weight:700;font-size:16px}
.primary:disabled{opacity:.6}
.fine{color:var(--muted);font-size:12.5px;text-align:center;margin:10px 0 0}

/* ---------- chat ---------- */
#app{display:flex;flex-direction:column;height:100vh;height:100dvh;max-width:900px;margin:0 auto;background:var(--bg);position:relative}
.top{display:flex;align-items:center;gap:10px;padding:10px 12px;padding-top:calc(10px + env(safe-area-inset-top));background:var(--accent);color:#fff}
.gav{width:40px;height:40px;border-radius:50%;background:rgba(255,255,255,.22);display:grid;place-items:center;font-size:20px;flex:none}
.ttl{flex:1;min-width:0;display:flex;flex-direction:column}
.ttl b{font-size:16.5px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.ttl span{font-size:12.5px;opacity:.85}
.ibtn{border:0;background:none;width:40px;height:40px;border-radius:50%;font-size:19px;flex:none}
.top .ibtn:hover,.bar .ibtn:hover{background:rgba(127,127,127,.18)}
#msgs{flex:1;overflow-y:auto;padding:10px 10px 14px;display:flex;flex-direction:column;overscroll-behavior:contain}
.empty{margin:auto;text-align:center;color:var(--muted)}
.day{text-align:center;margin:14px 0 6px}
.day span{background:var(--panel);color:var(--muted);font-size:12px;padding:3px 11px;border-radius:99px;box-shadow:var(--shadow)}
.msg{display:flex;align-items:flex-end;gap:7px;margin-top:2px}
.msg.first{margin-top:10px}
.msg.me{justify-content:flex-end}
.av{width:32px;height:32px;flex:none;border-radius:50%;color:#fff;display:grid;place-items:center;font-weight:700;font-size:14px}
.av.ghost{visibility:hidden}
.bub{max-width:min(80%,520px);background:var(--other);border-radius:15px;padding:6px 10px 4px;box-shadow:var(--shadow);min-width:0}
.me .bub{background:var(--me)}
.name{font-size:12.5px;font-weight:700;margin-bottom:2px}
.txt{white-space:pre-wrap;overflow-wrap:anywhere;line-height:1.42}
.txt a{color:var(--accent-d)}
.meta{display:flex;gap:7px;justify-content:flex-end;align-items:center;font-size:11px;color:var(--muted);margin-top:2px}
.del{border:0;background:none;padding:0;font-size:12px;opacity:.55}
.del:hover{opacity:1}
.pic{display:block;max-width:100%;max-height:340px;border-radius:10px;cursor:zoom-in;margin:2px 0 4px;min-width:140px;min-height:80px;background:var(--line);object-fit:cover}
.vid{display:block;width:100%;max-width:360px;max-height:380px;border-radius:10px;background:#000;margin:2px 0 4px}
.aud{min-width:230px}
.aud .lbl{font-size:13px;color:var(--muted);margin-bottom:2px;overflow-wrap:anywhere}
.aud audio{width:100%;height:40px;display:block}
.gone .gtxt{color:var(--muted);font-style:italic}
.prog{height:5px;border-radius:5px;background:var(--line);margin:6px 0 4px;overflow:hidden;min-width:180px}
.prog i{display:block;height:100%;width:0;background:var(--accent);transition:width .15s}
#jump{position:absolute;right:14px;bottom:78px;width:42px;height:42px;border-radius:50%;border:0;background:var(--panel);color:var(--accent);box-shadow:0 2px 8px rgba(0,0,0,.3);font-size:18px}

.bar{display:flex;align-items:flex-end;gap:8px;padding:8px 10px;padding-bottom:calc(8px + env(safe-area-inset-bottom));background:var(--panel);border-top:1px solid var(--line)}
.bar textarea{flex:1;resize:none;border:1px solid var(--line);border-radius:21px;padding:10px 15px;font-size:16px;background:var(--bg);max-height:140px;outline:none;line-height:1.35}
.bar textarea:focus{border-color:var(--accent)}
.send{width:42px;height:42px;border-radius:50%;border:0;background:var(--accent);color:#fff;font-size:18px;flex:none}
.send:disabled{opacity:.6}
.attach{position:relative}
#menu{position:absolute;bottom:50px;left:0;background:var(--panel);border:1px solid var(--line);border-radius:12px;box-shadow:0 6px 24px rgba(0,0,0,.25);padding:6px;min-width:170px;z-index:5}
#menu button{display:block;width:100%;text-align:left;border:0;background:none;padding:10px 12px;border-radius:8px}
#menu button:hover{background:var(--bg)}
.rec{align-items:center}
.rec .dot{width:11px;height:11px;border-radius:50%;background:var(--danger);animation:blink 1s infinite}
.rec .grow{flex:1;color:var(--muted)}
@keyframes blink{50%{opacity:.25}}

/* ---------- side panel ---------- */
#panel{position:fixed;inset:0;background:rgba(0,0,0,.45);display:flex;justify-content:flex-end;z-index:20}
.sheet{width:min(440px,100%);height:100%;background:var(--panel);display:flex;flex-direction:column}
.shead{display:flex;align-items:center;padding:10px 12px;padding-top:calc(10px + env(safe-area-inset-top));border-bottom:1px solid var(--line);gap:6px}
.shead .tabs{flex:1;margin:0}
#pBody{flex:1;overflow-y:auto;padding:8px 12px 20px}
.mem{display:flex;align-items:center;gap:10px;padding:9px 2px;border-bottom:1px solid var(--line)}
.mem .who{flex:1;min-width:0}
.mem .who b{display:block;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.mem .who small{color:var(--muted)}
.dotg{width:10px;height:10px;border-radius:50%;background:var(--line);flex:none}
.dotg.on{background:var(--ok)}
.badge{font-size:11px;font-weight:700;padding:2px 7px;border-radius:99px;background:var(--accent);color:#fff;margin-left:6px;vertical-align:1px}
.badge.red{background:var(--danger)}
.ucard{border:1px solid var(--line);border-radius:12px;padding:10px 12px;margin:10px 0;font-size:13.5px;line-height:1.5}
.ucard .row1{display:flex;align-items:center;gap:6px;font-size:15px}
.ucard .row1 b{flex:1;min-width:0;overflow-wrap:anywhere}
.ucard dl{margin:6px 0;display:grid;grid-template-columns:92px 1fr;gap:1px 8px}
.ucard dt{color:var(--muted)}
.ucard dd{margin:0;overflow-wrap:anywhere}
.ucard button{border:1px solid var(--line);background:var(--bg);padding:6px 12px;border-radius:8px}
.ucard button.danger{color:var(--danger);border-color:var(--danger)}
.dl{display:inline-block;margin:10px 0 0;color:var(--accent-d);font-weight:600}
#viewer{position:fixed;inset:0;background:rgba(0,0,0,.92);display:grid;place-items:center;z-index:30;cursor:zoom-out}
#viewer img{max-width:96vw;max-height:94vh;border-radius:6px}
#toast{position:fixed;left:50%;bottom:90px;transform:translate(-50%,20px);background:#222;color:#fff;padding:10px 16px;border-radius:12px;opacity:0;pointer-events:none;transition:.2s;z-index:40;max-width:90vw;text-align:center;font-size:14px}
#toast.show{opacity:1;transform:translate(-50%,0)}
#toast.bad{background:var(--danger)}
</style>
</head>
<body data-mode="login">

<div id="auth" class="auth">
  <form class="card" id="authForm">
    <div class="logo">&#128172;</div>
    <h1 id="gName">Group Chat</h1>
    <p class="sub">Sign in to join the conversation</p>
    <div class="tabs">
      <button type="button" id="tabLogin" class="on">Sign in</button>
      <button type="button" id="tabReg">Create account</button>
    </div>
    <div class="regonly"><label>Full name<input id="fName" maxlength="40" autocomplete="name"></label></div>
    <label><span id="uLabel">Username or email</span><input id="fUser" maxlength="120" autocapitalize="none" autocorrect="off" spellcheck="false" autocomplete="username"></label>
    <div class="regonly">
      <label>Email<input id="fEmail" type="email" maxlength="120" autocomplete="email"></label>
      <label>Phone (optional)<input id="fPhone" type="tel" maxlength="20" autocomplete="tel"></label>
    </div>
    <label>Password<input id="fPass" type="password" maxlength="100" autocomplete="current-password"></label>
    <div class="regonly">
      <label>Confirm password<input id="fPass2" type="password" maxlength="100" autocomplete="new-password"></label>
      <label id="inviteRow" hidden>Invite code<input id="fInvite" maxlength="60" autocomplete="off"></label>
    </div>
    <div id="authErr" class="err" role="alert"></div>
    <button class="primary" id="authBtn">Sign in</button>
    <p class="fine" id="firstNote"></p>
  </form>
</div>

<div id="app" hidden>
  <header class="top">
    <div class="gav">&#128172;</div>
    <div class="ttl"><b id="hName"></b><span id="hSub"></span></div>
    <button class="ibtn" id="btnMembers" title="Members">&#128101;</button>
    <button class="ibtn" id="btnLogout" title="Sign out">&#10162;</button>
  </header>
  <main id="msgs"></main>
  <button id="jump" hidden title="Latest messages">&#8595;</button>

  <footer class="bar" id="composer">
    <div class="attach">
      <button class="ibtn" id="btnPlus" title="Attach">&#10133;</button>
      <div id="menu" hidden>
        <button data-k="image">&#128247; Photo</button>
        <button data-k="video">&#127916; Video</button>
        <button data-k="audio">&#127925; Audio file</button>
      </div>
    </div>
    <textarea id="txt" rows="1" maxlength="2000" placeholder="Type a message"></textarea>
    <button class="send" id="btnSend" hidden title="Send">&#10148;</button>
    <button class="send" id="btnMic" title="Record a voice message">&#127908;</button>
  </footer>
  <footer class="bar rec" id="recbar" hidden>
    <button class="ibtn" id="recCancel" title="Cancel">&#128465;</button>
    <span class="dot"></span><b id="recTime">0:00</b><span class="grow">Recording&hellip;</span>
    <button class="send" id="recSend" title="Send voice message">&#10148;</button>
  </footer>
  <input type="file" id="fileIn" hidden>
</div>

<aside id="panel" hidden>
  <div class="sheet">
    <div class="shead"><div class="tabs" id="pTabs"></div><button class="ibtn" id="pClose" title="Close">&#10005;</button></div>
    <div id="pBody"></div>
  </div>
</aside>
<div id="viewer" hidden><img alt=""></div>
<div id="toast"></div>

<script>
(function(){
'use strict';
function $(id){return document.getElementById(id);}
function h(tag,cls,text){var e=document.createElement(tag);if(cls)e.className=cls;if(text!=null)e.textContent=text;return e;}
var S={me:null,cfg:null,byId:{},list:[],els:{},hasMore:false,es:null,members:[],online:[],lastId:0,loadingOlder:false,opened:false,stick:true,sending:false,tab:'members'};
var box=$('msgs');
var coarse=!!(window.matchMedia&&window.matchMedia('(pointer:coarse)').matches);

function toast(msg,bad){var t=$('toast');t.textContent=msg;t.className='show'+(bad?' bad':'');clearTimeout(toast.t);toast.t=setTimeout(function(){t.className='';},3800);}
function api(method,url,body){
  var o={method:method,headers:{'x-chat':'1'},credentials:'same-origin'};
  if(body!==undefined){o.headers['Content-Type']='application/json';o.body=JSON.stringify(body);}
  return fetch(url,o).then(function(r){
    return r.json().catch(function(){return {};}).then(function(j){
      if(!r.ok){var e=new Error(j.error||('Error '+r.status));e.status=r.status;throw e;}
      return j;
    });
  });
}
function two(n){return n<10?'0'+n:''+n;}
function fmtTime(ts){var d=new Date(ts);return two(d.getHours())+':'+two(d.getMinutes());}
function fmtDate(ts){return ts?new Date(ts).toLocaleString([], {day:'numeric',month:'short',year:'numeric',hour:'2-digit',minute:'2-digit'}):'-';}
function sameDay(a,b){var x=new Date(a),y=new Date(b);return x.getFullYear()===y.getFullYear()&&x.getMonth()===y.getMonth()&&x.getDate()===y.getDate();}
function dayLabel(ts){
  var n=new Date(),y=new Date(n.getFullYear(),n.getMonth(),n.getDate()-1);
  if(sameDay(ts,n.getTime()))return 'Today';
  if(sameDay(ts,y.getTime()))return 'Yesterday';
  return new Date(ts).toLocaleDateString([], {weekday:'short',day:'numeric',month:'short',year:'numeric'});
}
function fmtDur(s){s=Math.round(s||0);return Math.floor(s/60)+':'+two(s%60);}
function fmtSize(b){return b>=1048576?(b/1048576).toFixed(1)+' MB':Math.max(1,Math.round(b/1024))+' KB';}
function hue(name){var s=0,i;for(i=0;i<name.length;i++){s=(s*31+name.charCodeAt(i))|0;}return Math.abs(s)%360;}
function initial(name){var a=Array.from(name||'?');return (a[0]||'?').toUpperCase();}

function linkify(parent,text){
  var re=/(https?:\/\/[^\s<>"']+|www\.[^\s<>"']+)/gi,last=0,m;
  while((m=re.exec(text))){
    if(m.index>last)parent.appendChild(document.createTextNode(text.slice(last,m.index)));
    var raw=m[0],trail='',tm=/[.,;:!?)\]}]+$/.exec(raw);
    if(tm){trail=tm[0];raw=raw.slice(0,raw.length-trail.length);}
    var a=h('a',null,raw);
    a.href=/^www\./i.test(raw)?'https://'+raw:raw;
    a.target='_blank';a.rel='noopener noreferrer nofollow';
    parent.appendChild(a);
    if(trail)parent.appendChild(document.createTextNode(trail));
    last=m.index+m[0].length;
  }
  if(last<text.length)parent.appendChild(document.createTextNode(text.slice(last)));
}

/* ---------------- sign in / register ---------------- */
var mode='login';
function setMode(m){
  mode=m;document.body.setAttribute('data-mode',m);
  $('tabLogin').className=m==='login'?'on':'';
  $('tabReg').className=m==='reg'?'on':'';
  $('authBtn').textContent=m==='login'?'Sign in':'Create account';
  $('uLabel').textContent=m==='login'?'Username or email':'Choose a username';
  $('fPass').setAttribute('autocomplete',m==='login'?'current-password':'new-password');
  $('authErr').textContent='';
}
$('tabLogin').onclick=function(){setMode('login');};
$('tabReg').onclick=function(){setMode('reg');};
$('authForm').addEventListener('submit',function(e){
  e.preventDefault();
  var err=$('authErr');err.textContent='';
  var url,body;
  if(mode==='login'){
    url='/api/login';body={username:$('fUser').value.trim(),password:$('fPass').value};
  }else{
    if($('fPass').value!==$('fPass2').value){err.textContent='The two passwords do not match.';return;}
    url='/api/register';
    body={name:$('fName').value,username:$('fUser').value.trim(),email:$('fEmail').value,phone:$('fPhone').value,password:$('fPass').value,invite:$('fInvite').value};
  }
  $('authBtn').disabled=true;
  api('POST',url,body).then(function(u){S.me=u;enterApp();}).catch(function(e){err.textContent=e.message;}).then(function(){$('authBtn').disabled=false;});
});

function showAuth(msg){
  if(S.es){S.es.close();S.es=null;}
  S.opened=false;S.me=null;
  $('app').hidden=true;$('panel').hidden=true;$('auth').hidden=false;
  $('authErr').textContent=msg||'';
}
function handleErr(e){if(e&&e.status===401)showAuth('Your session ended. Please sign in again.');else toast((e&&e.message)||'Something went wrong',true);}

/* ---------------- app ---------------- */
function enterApp(){
  $('auth').hidden=true;$('app').hidden=false;
  $('fPass').value='';$('fPass2').value='';
  $('hName').textContent=S.cfg.group;
  S.byId={};S.list=[];S.els={};S.lastId=0;S.opened=false;
  loadMembers();
  api('GET','/api/messages?limit=60').then(function(r){
    r.messages.forEach(function(m){S.byId[m.id]=m;S.list.push(m);S.lastId=Math.max(S.lastId,m.id);});
    S.hasMore=r.hasMore;
    renderAll();scrollBottom();
    connect();
  }).catch(handleErr);
}

function updateSub(){
  var n=S.members.length,o=S.online.length;
  $('hSub').textContent=n+' member'+(n===1?'':'s')+' \u2022 '+o+' online';
}
function loadMembers(){
  api('GET','/api/members').then(function(r){
    S.members=r.members;S.online=r.online;updateSub();
    if(!$('panel').hidden&&S.tab==='members')renderPanel();
  }).catch(function(){});
}

function connect(){
  if(S.es)S.es.close();
  var es=new EventSource('/api/stream');S.es=es;
  es.addEventListener('open',function(){
    if(S.opened){
      api('GET','/api/messages?after='+S.lastId).then(function(r){r.messages.forEach(addMessage);}).catch(function(){});
    }
    S.opened=true;
  });
  es.addEventListener('msg',function(ev){addMessage(JSON.parse(ev.data));});
  es.addEventListener('del',function(ev){applyDelete(JSON.parse(ev.data).id);});
  es.addEventListener('presence',function(ev){S.online=JSON.parse(ev.data).online;updateSub();if(!$('panel').hidden&&S.tab==='members')renderPanel();});
  es.addEventListener('member',function(){loadMembers();if(!$('panel').hidden&&S.tab==='admin')renderPanel();});
  es.addEventListener('kicked',function(){showAuth('Your account has been suspended by the admin.');});
  es.onerror=function(){api('GET','/api/me').catch(function(e){if(e.status===401)showAuth('Your session ended. Please sign in again.');});};
}

/* ---------------- messages ---------------- */
function isNearBottom(){return box.scrollHeight-box.scrollTop-box.clientHeight<140;}
function scrollBottom(){box.scrollTop=box.scrollHeight;S.stick=true;$('jump').hidden=true;}
box.addEventListener('scroll',function(){
  S.stick=isNearBottom();$('jump').hidden=S.stick;
  if(box.scrollTop<60&&S.hasMore&&!S.loadingOlder&&S.list.length)loadOlder();
});
$('jump').onclick=scrollBottom;

function buildItems(m,prev){
  var out=[];
  var newDay=!prev||!sameDay(prev.ts,m.ts);
  if(newDay){var d=h('div','day');d.appendChild(h('span',null,dayLabel(m.ts)));out.push(d);}
  var first=newDay||prev.uid!==m.uid||m.ts-prev.ts>5*60000;
  var el=buildMsg(m,first);
  S.els[m.id]=el;out.push(el);
  return out;
}

function buildMsg(m,first){
  var isMe=m.uid===S.me.id;
  var row=h('div','msg'+(isMe?' me':'')+(first?' first':''));
  var hu=hue(m.username||'');
  if(!isMe){
    var av=h('div','av'+(first?'':' ghost'),first?initial(m.name):'');
    if(first)av.style.background='hsl('+hu+',55%,46%)';
    row.appendChild(av);
  }
  var b=h('div','bub');
  if(!isMe&&first){var nm=h('div','name',m.name);nm.style.color='hsl('+hu+',60%,42%)';b.appendChild(nm);}
  if(m.type==='deleted'){
    b.className+=' gone';b.appendChild(h('div','gtxt','This message was deleted'));
  }else{
    var md=m.media;
    if(m.type==='image'&&md){
      var img=h('img','pic');img.loading='lazy';img.alt=md.name||'photo';img.src=md.url;
      img.addEventListener('load',function(){if(S.stick)box.scrollTop=box.scrollHeight;});
      img.addEventListener('click',function(){openViewer(md.url);});
      b.appendChild(img);
    }else if(m.type==='video'&&md){
      var v=document.createElement('video');v.className='vid';v.controls=true;v.preload='metadata';v.setAttribute('playsinline','');v.src=md.url;
      v.addEventListener('loadedmetadata',function(){if(S.stick)box.scrollTop=box.scrollHeight;});
      b.appendChild(v);
    }else if(m.type==='audio'&&md){
      var w=h('div','aud');
      w.appendChild(h('div','lbl',md.voice?('Voice message \u2022 '+fmtDur(md.dur)):((md.name||'Audio')+' \u2022 '+fmtSize(md.size))));
      var au=document.createElement('audio');au.controls=true;au.preload='metadata';au.src=md.url;
      w.appendChild(au);b.appendChild(w);
    }
    if(m.text){var t=h('div','txt');linkify(t,m.text);b.appendChild(t);}
  }
  var meta=h('div','meta');meta.appendChild(h('span',null,fmtTime(m.ts)));
  if(m.type!=='deleted'&&(isMe||S.me.role==='admin')){
    var del=h('button','del','\uD83D\uDDD1');del.title='Delete';
    del.addEventListener('click',function(){
      if(confirm('Delete this message for everyone?'))api('POST','/api/delete',{id:m.id}).catch(handleErr);
    });
    meta.appendChild(del);
  }
  b.appendChild(meta);row.appendChild(b);
  return row;
}

function renderAll(){
  box.textContent='';S.els={};
  if(!S.list.length){box.appendChild(h('div','empty','No messages yet.\nSay hello \uD83D\uDC4B'));return;}
  var prev=null;
  S.list.forEach(function(m){buildItems(m,prev).forEach(function(e){box.appendChild(e);});prev=m;});
}

function addMessage(m){
  if(S.byId[m.id])return;
  var stick=isNearBottom()||m.uid===S.me.id;
  var prev=S.list.length?S.list[S.list.length-1]:null;
  var emptyEl=box.querySelector('.empty');if(emptyEl)emptyEl.remove();
  S.byId[m.id]=m;S.list.push(m);S.lastId=Math.max(S.lastId,m.id);
  buildItems(m,prev).forEach(function(e){box.appendChild(e);});
  if(stick)scrollBottom();else $('jump').hidden=false;
}

function applyDelete(id){
  var m=S.byId[id];if(!m)return;
  m.type='deleted';m.text='';m.media=null;
  var old=S.els[id];if(!old)return;
  var neu=buildMsg(m,old.classList.contains('first'));
  old.parentNode.replaceChild(neu,old);S.els[id]=neu;
}

function loadOlder(){
  S.loadingOlder=true;
  api('GET','/api/messages?limit=50&before='+S.list[0].id).then(function(r){
    var prevH=box.scrollHeight,prevTop=box.scrollTop;
    S.hasMore=r.hasMore;
    var add=r.messages.filter(function(m){return !S.byId[m.id];});
    add.forEach(function(m){S.byId[m.id]=m;});
    S.list=add.concat(S.list);
    S.stick=false;
    renderAll();
    box.scrollTop=box.scrollHeight-prevH+prevTop;
  }).catch(function(){}).then(function(){S.loadingOlder=false;});
}

/* ---------------- sending ---------------- */
var ta=$('txt');
function autosize(){ta.style.height='auto';ta.style.height=Math.min(ta.scrollHeight,140)+'px';}
function toggleSend(){var has=ta.value.trim().length>0;$('btnSend').hidden=!has;$('btnMic').hidden=has;}
ta.addEventListener('input',function(){autosize();toggleSend();});
ta.addEventListener('keydown',function(e){if(e.key==='Enter'&&!e.shiftKey&&!coarse){e.preventDefault();sendText();}});
$('btnSend').onclick=sendText;

function sendText(){
  var text=ta.value.trim();
  if(!text||S.sending)return;
  S.sending=true;$('btnSend').disabled=true;
  api('POST','/api/send',{text:text}).then(function(m){
    ta.value='';autosize();toggleSend();addMessage(m);
  }).catch(function(e){if(e.status===401)handleErr(e);else toast(e.message,true);})
  .then(function(){S.sending=false;$('btnSend').disabled=false;ta.focus();});
}

/* attach menu + file upload */
$('btnPlus').onclick=function(e){e.stopPropagation();$('menu').hidden=!$('menu').hidden;};
document.addEventListener('click',function(){$('menu').hidden=true;});
Array.prototype.forEach.call($('menu').querySelectorAll('button'),function(b){
  b.onclick=function(){
    var k=b.getAttribute('data-k');
    $('fileIn').setAttribute('accept',k+'/*');$('fileIn').setAttribute('data-k',k);
    $('fileIn').value='';$('fileIn').click();
  };
});
$('fileIn').addEventListener('change',function(){
  var f=this.files&&this.files[0];if(!f)return;
  uploadFile(f,this.getAttribute('data-k'),{});
  this.value='';
});

function addPending(kind,name){
  var row=h('div','msg me first'),b=h('div','bub');
  b.appendChild(h('div','txt','Uploading '+(kind==='image'?'photo':kind==='video'?'video':'audio')+(name&&name!=='voice-message'?' \u2022 '+name:'')+'\u2026'));
  var pr=h('div','prog'),bar=document.createElement('i');pr.appendChild(bar);b.appendChild(pr);
  row.appendChild(b);box.appendChild(row);scrollBottom();
  return {set:function(p){bar.style.width=p+'%';},remove:function(){row.remove();}};
}

function uploadFile(file,kind,opts){
  var limit=S.cfg.limits[kind];
  if(file.size>limit){toast('That file is too big (max '+Math.round(limit/1048576)+' MB).',true);return;}
  var caption=opts.voice?'':ta.value.trim().slice(0,500);
  function go(){
    var q='kind='+kind+'&name='+encodeURIComponent(file.name||'file')+'&caption='+encodeURIComponent(caption)+'&dur='+(opts.dur||0)+(opts.voice?'&voice=1':'');
    var p=addPending(kind,file.name);
    var x=new XMLHttpRequest();
    x.open('POST','/api/upload?'+q);
    x.setRequestHeader('x-chat','1');x.setRequestHeader('Content-Type','application/octet-stream');
    x.upload.onprogress=function(e){if(e.lengthComputable)p.set(Math.round(e.loaded*100/e.total));};
    x.onload=function(){
      p.remove();var j={};try{j=JSON.parse(x.responseText);}catch(e){}
      if(x.status===200){addMessage(j);if(caption){ta.value='';autosize();toggleSend();}}
      else if(x.status===401)handleErr({status:401});
      else toast(j.error||'Upload failed.',true);
    };
    x.onerror=function(){p.remove();toast('Upload failed. Check your connection.',true);};
    x.send(file);
  }
  if(caption)api('POST','/api/check',{text:caption}).then(go).catch(function(e){toast(e.message,true);});
  else go();
}

/* voice recording */
var rec=null;
function showComposer(){$('recbar').hidden=true;$('composer').hidden=false;}
$('btnMic').onclick=function(){
  if(!navigator.mediaDevices||!window.MediaRecorder){toast('Voice recording is not supported here. Use + then Audio file.',true);return;}
  if(!window.isSecureContext){toast('Voice recording needs HTTPS (or localhost). You can still send an audio file.',true);return;}
  navigator.mediaDevices.getUserMedia({audio:true}).then(function(stream){
    var types=['audio/webm;codecs=opus','audio/webm','audio/mp4','audio/ogg;codecs=opus'],mime='',i;
    for(i=0;i<types.length;i++){if(MediaRecorder.isTypeSupported(types[i])){mime=types[i];break;}}
    var mr=mime?new MediaRecorder(stream,{mimeType:mime}):new MediaRecorder(stream);
    var chunks=[],t0=Date.now();
    var r={mr:mr,cancel:false,timer:null};rec=r;
    mr.ondataavailable=function(e){if(e.data&&e.data.size)chunks.push(e.data);};
    mr.onstop=function(){
      stream.getTracks().forEach(function(t){t.stop();});
      clearInterval(r.timer);showComposer();rec=null;
      if(r.cancel)return;
      var blob=new Blob(chunks,{type:mr.mimeType||mime||'audio/webm'});
      var dur=Math.round((Date.now()-t0)/1000);
      if(dur<1||blob.size<500){toast('Recording was too short.');return;}
      blob.name='voice-message';
      uploadFile(blob,'audio',{voice:true,dur:dur});
    };
    mr.start(250);
    $('composer').hidden=true;$('recbar').hidden=false;$('recTime').textContent='0:00';
    r.timer=setInterval(function(){
      var s=Math.round((Date.now()-t0)/1000);$('recTime').textContent=fmtDur(s);
      if(s>=300)mr.stop();
    },500);
  }).catch(function(){toast('Microphone permission was denied.',true);});
};
$('recCancel').onclick=function(){if(rec){rec.cancel=true;rec.mr.stop();}};
$('recSend').onclick=function(){if(rec)rec.mr.stop();};

/* ---------------- image viewer ---------------- */
function openViewer(url){$('viewer').firstElementChild.src=url;$('viewer').hidden=false;}
$('viewer').onclick=function(){$('viewer').hidden=true;};
document.addEventListener('keydown',function(e){if(e.key==='Escape'){$('viewer').hidden=true;$('panel').hidden=true;}});

/* ---------------- members / admin panel ---------------- */
function openPanel(tab){S.tab=tab||'members';$('panel').hidden=false;renderPanel();}
$('btnMembers').onclick=function(){openPanel('members');};
$('pClose').onclick=function(){$('panel').hidden=true;};
$('panel').addEventListener('click',function(e){if(e.target===$('panel'))$('panel').hidden=true;});
$('btnLogout').onclick=function(){
  if(!confirm('Sign out?'))return;
  api('POST','/api/logout',{}).catch(function(){}).then(function(){showAuth('');});
};

function renderPanel(){
  var tabs=$('pTabs');tabs.textContent='';
  var list=[['members','Members']];
  if(S.me.role==='admin')list.push(['admin','Admin']);
  list.forEach(function(t){
    var b=h('button',S.tab===t[0]?'on':'',t[1]);
    b.onclick=function(){S.tab=t[0];renderPanel();};
    tabs.appendChild(b);
  });
  var body=$('pBody');body.textContent='';
  if(S.tab==='admin'&&S.me.role==='admin')renderAdmin(body);else renderMembers(body);
}

function renderMembers(body){
  var on={};S.online.forEach(function(id){on[id]=true;});
  var arr=S.members.slice().sort(function(a,b){
    return (on[b.id]?1:0)-(on[a.id]?1:0)||a.name.localeCompare(b.name);
  });
  arr.forEach(function(m){
    var r=h('div','mem');
    var av=h('div','av',initial(m.name));av.style.background='hsl('+hue(m.username)+',55%,46%)';
    var who=h('div','who'),b=h('b',null,m.name+(m.id===S.me.id?' (you)':''));
    if(m.role==='admin')b.appendChild(h('span','badge','admin'));
    who.appendChild(b);who.appendChild(h('small',null,'@'+m.username));
    r.appendChild(av);r.appendChild(who);r.appendChild(h('span','dotg'+(on[m.id]?' on':'')));
    body.appendChild(r);
  });
}

function renderAdmin(body){
  body.appendChild(h('p','fine','Loading\u2026'));
  api('GET','/api/admin/users').then(function(r){
    if(S.tab!=='admin'||$('panel').hidden)return;
    body.textContent='';
    body.appendChild(h('p','fine',r.users.length+' registered users \u2022 '+r.totalMessages+' messages stored'));
    var a=h('a','dl','\u2B07 Download all user data (CSV)');a.href='/api/admin/users.csv';a.setAttribute('download','chat-users.csv');
    body.appendChild(a);
    r.users.forEach(function(u){
      var c=h('div','ucard'),top=h('div','row1'),nm=h('b',null,u.name);
      if(u.role==='admin')nm.appendChild(h('span','badge','admin'));
      if(u.banned)nm.appendChild(h('span','badge red','suspended'));
      top.appendChild(nm);top.appendChild(h('span','dotg'+(u.online?' on':'')));c.appendChild(top);
      var dl=document.createElement('dl');
      [['Username','@'+u.username],['Email',u.email],['Phone',u.phone||'-'],['Joined',fmtDate(u.joinedAt)],['Last login',fmtDate(u.lastLoginAt)],['Last IP',u.lastIp||'-'],['Messages',String(u.messages)],['Blocked links',String(u.strikes)]].forEach(function(p){
        dl.appendChild(h('dt',null,p[0]));dl.appendChild(h('dd',null,p[1]));
      });
      c.appendChild(dl);
      if(u.role!=='admin'){
        var b=h('button',u.banned?'':'danger',u.banned?'Restore account':'Suspend account');
        b.onclick=function(){
          if(!u.banned&&!confirm('Suspend '+u.name+'? They will be signed out and cannot log in.'))return;
          api('POST','/api/admin/ban',{id:u.id,banned:!u.banned}).then(function(){renderPanel();}).catch(handleErr);
        };
        c.appendChild(b);
      }
      body.appendChild(c);
    });
  }).catch(handleErr);
}

/* ---------------- start ---------------- */
api('GET','/api/config').then(function(cfg){
  S.cfg=cfg;document.title=cfg.group;$('gName').textContent=cfg.group;
  $('inviteRow').hidden=!cfg.inviteRequired;
  if(cfg.first){setMode('reg');$('firstNote').textContent='You are the first person here, so your account will be the group admin.';}
  return api('GET','/api/me').then(function(u){S.me=u;enterApp();},function(){/* not signed in: stay on the sign-in screen */});
}).catch(function(){$('authErr').textContent='Cannot reach the server. Please refresh.';});
})();
</script>
</body>
</html>
`, 'utf8');

const server = http.createServer((req, res) => {
  handle(req, res).catch((err) => {
    if (!err.status) console.error(err);
    try {
      if (!res.headersSent) fail(res, err.status || 500, err.status ? err.message : 'Server error');
      else res.end();
    } catch (e) {}
  });
});
server.requestTimeout = 0;        // allow slow uploads of big videos
server.keepAliveTimeout = 65000;

async function handle(req, res) {
  const url = new URL(req.url, 'http://localhost');
  const p = url.pathname;
  res.setHeader('X-Content-Type-Options', 'nosniff');
  res.setHeader('Referrer-Policy', 'no-referrer');

  if (req.method === 'GET' && (p === '/' || p === '/index.html')) {
    res.writeHead(200, {
      'Content-Type': 'text/html; charset=utf-8',
      'Content-Length': PAGE_BUF.length,
      'Cache-Control': 'no-store',
      'Content-Security-Policy': "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; img-src 'self' data: blob:; media-src 'self' blob:; connect-src 'self'; frame-ancestors 'none'; base-uri 'none'; form-action 'self'",
      'Permissions-Policy': 'microphone=(self), camera=(), geolocation=()'
    });
    return res.end(PAGE_BUF);
  }
  if (p === '/favicon.ico') { res.writeHead(204); return res.end(); }
  if (p.startsWith('/api/')) return api(req, res, url);
  if ((req.method === 'GET' || req.method === 'HEAD') && p.startsWith('/media/')) return serveMedia(req, res, p);
  return fail(res, 404, 'Not found');
}

function shutdown() {
  try { saveSessions(true); } catch (e) {}
  process.exit(0);
}
process.on('SIGINT', shutdown);
process.on('SIGTERM', shutdown);
process.on('uncaughtException', (e) => console.error('Unexpected error:', e));

server.listen(PORT, HOST, () => {
  console.log('\n  ' + GROUP_NAME + ' is running');
  console.log('  -> http://localhost:' + PORT);
  const nets = os.networkInterfaces();
  Object.keys(nets).forEach((n) => nets[n].forEach((i) => {
    if (i.family === 'IPv4' && !i.internal) console.log('  -> http://' + i.address + ':' + PORT + '   (same Wi-Fi / network)');
  }));
  console.log('  Data folder: ' + DATA_DIR);
  console.log('  The first account you create becomes the admin.\n');
});
