// main.ts is mend, the CLI SPEC.md specifies. Node 22, the standard library alone;
// run it as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

/** A patch's lines: split at \n, one trailing \r removed, no empty piece after a final \n. */
function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Move = [string, string];
type Edit = (tree: Tree, moves: Move[]) => void;

// ---------------------------------------------------------------- text helpers

const leadWs = (s: string): string => /^[ \t]*/.exec(s)![0];
const stripTrail = (s: string): string => s.replace(/[ \t]+$/, '');
const stripBoth = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');

interface FileText {
  lines: string[];
  br: string;
  final: boolean;
}

function splitFile(text: string): FileText {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const lines = text.split(br);
  const final = text.endsWith(br);
  if (final) lines.pop();
  return { lines, br, final };
}

function joinFile(lines: string[], br: string, final: boolean): string {
  if (lines.length === 0) return '';
  return lines.join(br) + (final ? br : '');
}

// ------------------------------------------------------------- line matching

function normAt(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return stripTrail(s);
  return stripBoth(s);
}

function occurrences(file: string[], o: string[], tier: number): number[] {
  const out: number[] = [];
  if (o.length === 0) return out;
  const f = tier === 0 ? file : file.map((l) => normAt(l, tier));
  const p = tier === 0 ? o : o.map((l) => normAt(l, tier));
  for (let i = 0; i + p.length <= f.length; i += 1) {
    let ok = true;
    for (let j = 0; j < p.length; j += 1) {
      if (f[i + j] !== p[j]) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

function tiers(strict: boolean): number[] {
  return strict ? [0] : [0, 1, 2];
}

/** The first tier at which O occurs at least once, with those occurrences. */
function findTier(file: string[], o: string[], strict: boolean): { tier: number; pos: number[] } | null {
  if (o.length === 0) return null;
  for (const tier of tiers(strict)) {
    const pos = occurrences(file, o, tier);
    if (pos.length > 0) return { tier, pos };
  }
  return null;
}

interface Entry {
  kind: 'ctx' | 'del' | 'add';
  text: string;
}

function hunkEntries(body: string[]): Entry[] {
  const out: Entry[] = [];
  for (const l of body) {
    if (l === '') out.push({ kind: 'ctx', text: '' });
    else if (l[0] === ' ') out.push({ kind: 'ctx', text: l.slice(1) });
    else if (l[0] === '-') out.push({ kind: 'del', text: l.slice(1) });
    else if (l[0] === '+') out.push({ kind: 'add', text: l.slice(1) });
  }
  return out;
}

function entriesToO(entries: Entry[]): string[] {
  const o: string[] = [];
  for (const e of entries) if (e.kind !== 'add') o.push(e.text);
  return o;
}

interface NItem {
  text: string;
  /** index in O of the matching context line, or -1 for a line of N alone */
  ctx: number;
}

function entriesToN(entries: Entry[]): NItem[] {
  const n: NItem[] = [];
  let oi = 0;
  for (const e of entries) {
    if (e.kind === 'add') n.push({ text: e.text, ctx: -1 });
    else {
      if (e.kind === 'ctx') n.push({ text: e.text, ctx: oi });
      oi += 1;
    }
  }
  return n;
}

function buildN(n: NItem[], fileLines: string[], pos: number, oFirst: string, tier: number): string[] {
  const P = tier === 2 ? leadWs(oFirst) : '';
  const F = tier === 2 ? leadWs(fileLines[pos] ?? '') : '';
  const out: string[] = [];
  for (const it of n) {
    if (it.ctx >= 0) {
      out.push(fileLines[pos + it.ctx] ?? it.text);
      continue;
    }
    let t = it.text;
    if (tier === 2 && t !== '' && t.trim() !== '' && t.startsWith(P)) t = F + t.slice(P.length);
    out.push(t);
  }
  return out;
}

/** Whether a `\` line follows the hunk's last context or `+` line. */
function noEolAfterLastN(body: string[]): boolean {
  let lastN = -1;
  for (let k = 0; k < body.length; k += 1) {
    const b = body[k]!;
    if (b === '' || b[0] === ' ' || b[0] === '+') lastN = k;
  }
  return lastN >= 0 && (body[lastN + 1] ?? '').startsWith('\\');
}

// ------------------------------------------------------------ format detection

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---------------------------------------------------------------- unified diffs

interface Ref {
  p: string | null;
  dn: boolean;
  set: boolean;
}

const NO_REF: Ref = { p: null, dn: false, set: false };

function unPath(s: string): Ref {
  let p = s;
  const tab = p.indexOf('\t');
  if (tab >= 0) p = p.slice(0, tab);
  p = p.trim();
  if (p === '/dev/null') return { p: null, dn: true, set: true };
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return { p, dn: false, set: true };
}

interface Hunk {
  a: number;
  body: string[];
  noEol: boolean;
}

interface Section {
  gitOld: Ref;
  gitNew: Ref;
  pairOld: Ref;
  pairNew: Ref;
  renameOld: Ref;
  renameNew: Ref;
  newFileMode: boolean;
  deletedFileMode: boolean;
  hunks: Hunk[];
  line: number;
}

function newSection(): Section {
  return {
    gitOld: NO_REF,
    gitNew: NO_REF,
    pairOld: NO_REF,
    pairNew: NO_REF,
    renameOld: NO_REF,
    renameNew: NO_REF,
    newFileMode: false,
    deletedFileMode: false,
    hunks: [],
    line: 0,
  };
}

const HUNK_RE = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/;

function applyUnifiedHunks(lines: string[], finalBreak: boolean, hunks: Hunk[], path: string, strict: boolean): { lines: string[]; final: boolean } {
  let d = 0;
  let fin = finalBreak;
  let cur = lines;
  for (const h of hunks) {
    const entries = hunkEntries(h.body);
    const oLines = entriesToO(entries);
    const n = entriesToN(entries);
    if (oLines.length === 0) {
      const pos = Math.max(0, Math.min(h.a + d, cur.length));
      const atEnd = pos === cur.length;
      const rep = buildN(n, cur, pos, '', 0);
      cur = [...cur.slice(0, pos), ...rep, ...cur.slice(pos)];
      if (atEnd) fin = !h.noEol;
      d += n.length;
      continue;
    }
    const r = findTier(cur, oLines, strict);
    if (r === null) throw new Fail('no-match', path);
    const target = h.a - 1 + d;
    let best = r.pos[0]!;
    for (const q of r.pos) if (Math.abs(q - target) < Math.abs(best - target)) best = q;
    const matchedEnd = best + oLines.length === cur.length;
    const rep = buildN(n, cur, best, oLines[0]!, r.tier);
    cur = [...cur.slice(0, best), ...rep, ...cur.slice(best + oLines.length)];
    if (matchedEnd) fin = !h.noEol;
    d += n.length - oLines.length;
  }
  return { lines: cur, final: fin };
}

function createdText(hunks: Hunk[]): string {
  const out: string[] = [];
  let lastPlusHadEscape = false;
  let any = false;
  for (const h of hunks) {
    for (let k = 0; k < h.body.length; k += 1) {
      const l = h.body[k]!;
      if (l !== '' && l[0] === '+') {
        out.push(l.slice(1));
        any = true;
        lastPlusHadEscape = (h.body[k + 1] ?? '').startsWith('\\');
      }
    }
  }
  if (!any) return '';
  return out.join('\n') + (lastPlusHadEscape ? '' : '\n');
}

function makeSectionEdit(sec: Section, strict: boolean): Edit {
  return (tree, moves) => {
    const o = sec.pairOld.set ? sec.pairOld : sec.renameOld.set ? sec.renameOld : sec.gitOld;
    const nw = sec.pairNew.set ? sec.pairNew : sec.renameNew.set ? sec.renameNew : sec.gitNew;
    const creation = o.dn || sec.newFileMode;
    const deletion = nw.dn || sec.deletedFileMode;
    if (creation) {
      const p = nw.p;
      if (p === null || !safe(p)) throw new Fail('unsafe', p ?? '');
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, createdText(sec.hunks));
      return;
    }
    if (deletion) {
      const p = o.p;
      if (p === null || !safe(p)) throw new Fail('unsafe', p ?? '');
      if (tree.get(p) === null) throw new Fail('missing', p);
      tree.now.set(p, null);
      return;
    }
    const oldP = o.p;
    const newP = nw.p;
    // Section 10: every path the edit names is checked for safety before anything else about it.
    if (oldP === null || !safe(oldP)) throw new Fail('unsafe', oldP ?? '');
    if (newP !== null && !safe(newP)) throw new Fail('unsafe', newP);
    const t = tree.get(oldP);
    if (t === null) throw new Fail('missing', oldP);
    if (newP === null || oldP === newP) {
      const f = splitFile(t);
      const r = applyUnifiedHunks(f.lines, f.final, sec.hunks, oldP, strict);
      tree.now.set(oldP, joinFile(r.lines, f.br, r.final));
      return;
    }
    if (tree.get(newP) !== null) throw new Fail('exists', newP);
    const f = splitFile(t);
    const r = applyUnifiedHunks(f.lines, f.final, sec.hunks, oldP, strict);
    tree.now.set(oldP, null);
    tree.now.set(newP, joinFile(r.lines, f.br, r.final));
    moves.push([oldP, newP]);
  };
}

function parseUnified(lines: string[], strict: boolean): Edit[] {
  const sections: Section[] = [];
  let cur: Section | null = null;
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ')) {
      const m = /^diff --git a\/(.+?) b\/(.+)$/.exec(l);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      cur = newSection();
      cur.line = i + 1;
      cur.gitOld = { p: m[1]!, dn: false, set: true };
      cur.gitNew = { p: m[2]!, dn: false, set: true };
      sections.push(cur);
      i += 1;
      continue;
    }
    if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur === null || cur.hunks.length > 0 || cur.pairOld.set) {
        cur = newSection();
        cur.line = i + 1;
        sections.push(cur);
      }
      cur.pairOld = unPath(l.slice(4));
      cur.pairNew = unPath(lines[i + 1]!.slice(4));
      i += 2;
      continue;
    }
    if (l.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = HUNK_RE.exec(l);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const a = Number(m[1]);
      i += 1;
      const body: string[] = [];
      while (i < n) {
        const b = lines[i]!;
        if (b.startsWith('diff --git ')) break;
        if (b.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (b === '' || b[0] === ' ' || b[0] === '-' || b[0] === '+' || b[0] === '\\') {
          body.push(b);
          i += 1;
          continue;
        }
        break;
      }
      while (body.length > 0 && body[body.length - 1] === '') body.pop();
      cur.hunks.push({ a, body, noEol: noEolAfterLastN(body) });
      continue;
    }
    if (cur !== null && cur.hunks.length === 0) {
      if (l.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      if (l.startsWith('rename from ')) cur.renameOld = { p: l.slice(12).trim(), dn: false, set: true };
      else if (l.startsWith('rename to ')) cur.renameNew = { p: l.slice(10).trim(), dn: false, set: true };
      else if (l.startsWith('new file mode')) cur.newFileMode = true;
      else if (l.startsWith('deleted file mode')) cur.deletedFileMode = true;
      i += 1;
      continue;
    }
    i += 1;
  }
  if (sections.length === 0) throw new Exit2('error: parse 1');
  return sections.map((s) => makeSectionEdit(s, strict));
}

// ------------------------------------------------------- SEARCH/REPLACE blocks

interface SRBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
}

function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const blocks: SRBlock[] = [];
  let prevPath: string | null = null;
  let lastEnd = -1;
  let i = 0;
  const n = lines.length;
  while (i < n) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    let path: string | null = null;
    for (let k = i - 1; k > lastEnd; k -= 1) {
      const l = lines[k]!;
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) path = prevPath;
    if (path === null) throw new Exit2(`error: parse ${i + 1}`);
    let eq = -1;
    for (let k = i + 1; k < n; k += 1) {
      const t = lines[k]!.trimEnd();
      if (t === '=======') {
        eq = k;
        break;
      }
      if (t === '>>>>>>> REPLACE') throw new Exit2(`error: parse ${i + 1}`);
    }
    if (eq < 0) throw new Exit2(`error: parse ${i + 1}`);
    let rp = -1;
    for (let k = eq + 1; k < n; k += 1) {
      if (lines[k]!.trimEnd() === '>>>>>>> REPLACE') {
        rp = k;
        break;
      }
    }
    if (rp < 0) throw new Exit2(`error: parse ${i + 1}`);
    blocks.push({ path, oldLines: lines.slice(i + 1, eq), newLines: lines.slice(eq + 1, rp) });
    prevPath = path;
    lastEnd = rp;
    i = rp + 1;
  }
  if (blocks.length === 0) throw new Exit2('error: parse 1');
  return blocks.map((b) => makeSREdit(b, strict));
}

function makeSREdit(b: SRBlock, strict: boolean): Edit {
  return (tree) => {
    const p = b.path;
    if (!safe(p)) throw new Fail('unsafe', p);
    if (b.oldLines.length === 0) {
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, b.newLines.length === 0 ? '' : b.newLines.join('\n') + '\n');
      return;
    }
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    const f = splitFile(t);
    const r = findTier(f.lines, b.oldLines, strict);
    if (r === null) throw new Fail('no-match', p);
    if (r.pos.length > 1) throw new Fail('ambiguous', p);
    const pos = r.pos[0]!;
    const entries: Entry[] = b.newLines.map((x) => ({ kind: 'add' as const, text: x }));
    const rep = buildN(entriesToN(entries), f.lines, pos, b.oldLines[0]!, r.tier);
    const out = [...f.lines.slice(0, pos), ...rep, ...f.lines.slice(pos + b.oldLines.length)];
    tree.now.set(p, joinFile(out, f.br, f.final));
  };
}

// ------------------------------------------------------------------ V4A patches

interface V4AChunk {
  anchor: string | null;
  body: string[];
  eof: boolean;
}

interface V4ASection {
  kind: 'add' | 'del' | 'upd';
  path: string;
  moveTo: string | null;
  lines: string[];
  chunks: V4AChunk[];
  line: number;
}

const isBodyLine = (l: string): boolean => l === '' || l[0] === ' ' || l[0] === '-' || l[0] === '+';

function isSectionStart(l: string): boolean {
  return l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');
}

function parseV4A(lines: string[], strict: boolean): Edit[] {
  const n = lines.length;
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = n - 1; k >= 0; k -= 1) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${n + 1}`);

  const secs: V4ASection[] = [];
  let i = first + 1;
  while (i < last) {
    const l = lines[i]!;
    if (blank(l)) {
      i += 1;
      continue;
    }
    let kind: 'add' | 'del' | 'upd';
    let path: string;
    if (l.startsWith('*** Add File: ')) {
      kind = 'add';
      path = l.slice(14).trim();
    } else if (l.startsWith('*** Delete File: ')) {
      kind = 'del';
      path = l.slice(17).trim();
    } else if (l.startsWith('*** Update File: ')) {
      kind = 'upd';
      path = l.slice(17).trim();
    } else {
      throw new Exit2(`error: parse ${i + 1}`);
    }
    const startLine = i + 1;
    let j = i + 1;
    const content: number[] = [];
    while (j < last && !isSectionStart(lines[j]!)) {
      content.push(j);
      j += 1;
    }
    while (content.length > 0 && blank(lines[content[content.length - 1]!]!)) content.pop();

    const sec: V4ASection = { kind, path, moveTo: null, lines: [], chunks: [], line: startLine };
    if (kind === 'add') {
      for (const idx of content) {
        const b = lines[idx]!;
        if (b === '') sec.lines.push('');
        else if (b[0] === '+') sec.lines.push(b.slice(1));
        else throw new Exit2(`error: parse ${idx + 1}`);
      }
    } else if (kind === 'del') {
      if (content.length > 0) throw new Exit2(`error: parse ${content[0]! + 1}`);
    } else {
      let k = 0;
      if (content.length > 0 && lines[content[0]!]!.startsWith('*** Move to: ')) {
        sec.moveTo = lines[content[0]!]!.slice(13).trim();
        k = 1;
      }
      while (k < content.length) {
        const cl = lines[content[k]!]!;
        let anchor: string | null = null;
        if (cl.startsWith('@@')) {
          anchor = cl.slice(2).trim();
          if (anchor === '') anchor = null;
          k += 1;
        } else if (sec.chunks.length === 0 && isBodyLine(cl)) {
          anchor = null;
        } else {
          throw new Exit2(`error: parse ${content[k]! + 1}`);
        }
        const body: string[] = [];
        let eof = false;
        while (k < content.length) {
          const b = lines[content[k]!]!;
          if (b.startsWith('@@')) break;
          if (b.trim() === '*** End of File' && b[0] === '*') {
            eof = true;
            k += 1;
            break;
          }
          if (isBodyLine(b)) {
            body.push(b);
            k += 1;
            continue;
          }
          throw new Exit2(`error: parse ${content[k]! + 1}`);
        }
        sec.chunks.push({ anchor, body, eof });
      }
      if (sec.chunks.length === 0 && sec.moveTo === null) throw new Exit2(`error: parse ${startLine}`);
    }
    secs.push(sec);
    i = j;
  }
  if (secs.length === 0) throw new Exit2('error: parse 1');
  return secs.map((s) => makeV4AEdit(s, strict));
}

function findAnchor(lines: string[], anchor: string, cursor: number, strict: boolean): number | null {
  for (const tier of tiers(strict)) {
    for (let i = cursor; i < lines.length; i += 1) {
      if (normAt(lines[i]!, tier) === normAt(anchor, tier)) return i;
    }
  }
  return null;
}

function makeV4AEdit(sec: V4ASection, strict: boolean): Edit {
  return (tree, moves) => {
    const p = sec.path;
    if (!safe(p)) throw new Fail('unsafe', p);
    if (sec.kind === 'add') {
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, sec.lines.length === 0 ? '' : sec.lines.join('\n') + '\n');
      return;
    }
    if (sec.kind === 'del') {
      if (tree.get(p) === null) throw new Fail('missing', p);
      tree.now.set(p, null);
      return;
    }
    // Section 10: every path the edit names is checked for safety before anything else about it.
    if (sec.moveTo !== null && !safe(sec.moveTo)) throw new Fail('unsafe', sec.moveTo);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    let target = p;
    if (sec.moveTo !== null) {
      if (tree.get(sec.moveTo) !== null) throw new Fail('exists', sec.moveTo);
      target = sec.moveTo;
    }
    const f = splitFile(t);
    let cur = f.lines;
    let cursor = 0;
    for (const c of sec.chunks) {
      if (c.anchor !== null) {
        const hit = findAnchor(cur, c.anchor, cursor, strict);
        if (hit === null) throw new Fail('no-match', p);
        cursor = hit + 1;
      }
      const entries = hunkEntries(c.body);
      const oLines = entriesToO(entries);
      const nItems = entriesToN(entries);
      if (oLines.length === 0) {
        const pos = c.eof ? cur.length : Math.min(cursor, cur.length);
        const rep = buildN(nItems, cur, pos, '', 0);
        cur = [...cur.slice(0, pos), ...rep, ...cur.slice(pos)];
        cursor = pos + nItems.length;
        continue;
      }
      let found: { pos: number; tier: number } | null = null;
      for (const tier of tiers(strict)) {
        const occ = occurrences(cur, oLines, tier).filter((q) => q >= cursor && (!c.eof || q + oLines.length === cur.length));
        if (occ.length > 0) {
          found = { pos: occ[0]!, tier };
          break;
        }
      }
      if (found === null) throw new Fail('no-match', p);
      const rep = buildN(nItems, cur, found.pos, oLines[0]!, found.tier);
      cur = [...cur.slice(0, found.pos), ...rep, ...cur.slice(found.pos + oLines.length)];
      cursor = found.pos + nItems.length;
    }
    const text = joinFile(cur, f.br, f.final);
    if (sec.moveTo !== null) {
      tree.now.set(p, null);
      tree.now.set(target, text);
      moves.push([p, target]);
    } else {
      tree.now.set(p, text);
    }
  };
}

// -------------------------------------------------------------------- JSON edits

function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const need = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = need(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = need(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, joinFile(lines, br, final));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ------------------------------------------------------------------------ main

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else edits = parseV4A(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const moves: Move[] = [];
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesBefore = moves.length;
    try {
      edit(tree, moves);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      moves.length = movesBefore;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };

  const changed = new Map<string, 'A' | 'D' | 'M'>();
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    changed.set(p, was === null ? 'A' : now === null ? 'D' : 'M');
  }
  const writes = new Map(changed);
  const rows: { key: string; text: string }[] = [];
  const usedR = new Set<string>();
  for (const [oldP, newP] of moves) {
    if (usedR.has(oldP) || usedR.has(newP)) continue;
    if (changed.get(oldP) !== 'D' || changed.get(newP) !== 'A') continue;
    if (tree.original(oldP) === null || tree.now.get(oldP) !== null) continue;
    if (tree.original(newP) !== null || tree.now.get(newP) === null) continue;
    changed.delete(oldP);
    changed.delete(newP);
    usedR.add(oldP);
    usedR.add(newP);
    rows.push({ key: newP, text: `R ${oldP} -> ${newP}` });
  }
  for (const [p, k] of changed) rows.push({ key: p, text: `${k} ${p}` });
  rows.sort((x, y) => Buffer.compare(Buffer.from(x.key), Buffer.from(y.key)));

  if (!check) {
    for (const [p, k] of writes) {
      if (k === 'D') rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, tree.now.get(p)!);
      }
    }
  }
  const n = rows.length;
  return { code: 0, out: [...rows.map((r) => r.text), `ok: ${n} ${n === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
