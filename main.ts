// Tiny stack VM (ISA v1): faithful interpreter of the reference VM (vm.mjs).
// Reads /input/<id>/program.bin + input.bin, writes /output/<id>/stdout.bin + exit.txt.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const enc = new TextEncoder();

// Returns [stdoutBytes, exitCode]. stdoutBytes is a view into a fresh buffer.
function run(p, inp) {
  const n = p.length;
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let csp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let olen = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const done = (code) => [out.subarray(0, olen), code];
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = p[pc];
    switch (op) {
      case 0x00: // HALT
        steps++;
        return done(0);
      case 0x01: // PUSH8
        if (pc + 1 >= n) return done(9);
        steps++;
        if (sp + 1 > 256) return done(3);
        D[sp++] = (p[pc + 1] << 24) >> 24;
        pc += 2;
        break;
      case 0x02: // PUSH32
        if (pc + 4 >= n) return done(9);
        steps++;
        if (sp + 1 > 256) return done(3);
        D[sp++] = p[pc + 1] | (p[pc + 2] << 8) | (p[pc + 3] << 16) | (p[pc + 4] << 24);
        pc += 5;
        break;
      case 0x03: // POP
        steps++;
        if (sp < 1) return done(2);
        sp--;
        pc++;
        break;
      case 0x04: // DUP
        steps++;
        if (sp < 1) return done(2);
        if (sp + 1 > 256) return done(3);
        D[sp] = D[sp - 1];
        sp++;
        pc++;
        break;
      case 0x05: // SWAP
        steps++;
        if (sp < 2) return done(2);
        {
          const t = D[sp - 1];
          D[sp - 1] = D[sp - 2];
          D[sp - 2] = t;
        }
        pc++;
        break;
      case 0x06: // OVER
        steps++;
        if (sp < 2) return done(2);
        if (sp + 1 > 256) return done(3);
        D[sp] = D[sp - 2];
        sp++;
        pc++;
        break;
      case 0x07: // ROT
        steps++;
        if (sp < 3) return done(2);
        {
          const a = D[sp - 3];
          D[sp - 3] = D[sp - 2];
          D[sp - 2] = D[sp - 1];
          D[sp - 1] = a;
        }
        pc++;
        break;
      case 0x17: // NEG
        steps++;
        if (sp < 1) return done(2);
        D[sp - 1] = (-D[sp - 1]) | 0;
        pc++;
        break;
      case 0x1b: // NOT
        steps++;
        if (sp < 1) return done(2);
        D[sp - 1] = ~D[sp - 1];
        pc++;
        break;
      case 0x10: // ADD
      case 0x11: // SUB
      case 0x12: // MUL
      case 0x13: // DIV
      case 0x14: // MOD
      case 0x15: // DIVU
      case 0x16: // MODU
      case 0x18: // AND
      case 0x19: // OR
      case 0x1a: // XOR
      case 0x1c: // SHL
      case 0x1d: // SHR
      case 0x1e: // SHRU
      case 0x20: // EQ
      case 0x21: // LT
      case 0x22: // LTU
        steps++;
        if (sp < 2) return done(2);
        {
          const b = D[sp - 1];
          const a = D[sp - 2];
          let r;
          if (op === 0x10) r = (a + b) | 0;
          else if (op === 0x11) r = (a - b) | 0;
          else if (op === 0x12) r = Math.imul(a, b);
          else if (op === 0x13) {
            if (b === 0) return done(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
          } else if (op === 0x14) {
            if (b === 0) return done(4);
            r = b === -1 ? 0 : (a % b) | 0;
          } else if (op === 0x15) {
            if (b === 0) return done(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
          } else if (op === 0x16) {
            if (b === 0) return done(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
          } else if (op === 0x18) r = a & b;
          else if (op === 0x19) r = a | b;
          else if (op === 0x1a) r = a ^ b;
          else if (op === 0x1c) r = a << (b & 31);
          else if (op === 0x1d) r = a >> (b & 31);
          else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
          else if (op === 0x20) r = a === b ? 1 : 0;
          else if (op === 0x21) r = a < b ? 1 : 0;
          else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
          sp -= 2;
          D[sp++] = r;
        }
        pc++;
        break;
      case 0x30: // JMP
        if (pc + 2 >= n) return done(9);
        steps++;
        pc = pc + 3 + (((p[pc + 1] | (p[pc + 2] << 8)) << 16) >> 16);
        break;
      case 0x31: // JZ
      case 0x32: // JNZ
        if (pc + 2 >= n) return done(9);
        steps++;
        if (sp < 1) return done(2);
        {
          const v = D[--sp];
          const rel = ((p[pc + 1] | (p[pc + 2] << 8)) << 16) >> 16;
          pc = pc + 3;
          if ((op === 0x31) === (v === 0)) pc += rel;
        }
        break;
      case 0x33: // CALL
        if (pc + 2 >= n) return done(9);
        steps++;
        if (csp === 64) return done(7);
        C[csp++] = pc + 3;
        pc = p[pc + 1] | (p[pc + 2] << 8);
        break;
      case 0x34: // RET
        steps++;
        if (csp === 0) return done(8);
        pc = C[--csp];
        break;
      case 0x40: // LOAD
        steps++;
        if (sp < 1) return done(2);
        {
          const addr = D[sp - 1];
          if (addr < 0 || addr >= 256) return done(6);
          D[sp - 1] = M[addr];
        }
        pc++;
        break;
      case 0x41: // STORE
        steps++;
        if (sp < 2) return done(2);
        {
          const addr = D[sp - 1];
          const v = D[sp - 2];
          if (addr < 0 || addr >= 256) return done(6);
          sp -= 2;
          M[addr] = v;
        }
        pc++;
        break;
      case 0x50: // PRINT
        steps++;
        if (sp < 1) return done(2);
        {
          const bytes = enc.encode(String(D[sp - 1]));
          if (olen + bytes.length > 65536) return done(11);
          sp--;
          out.set(bytes, olen);
          olen += bytes.length;
        }
        pc++;
        break;
      case 0x51: // PUTC
        steps++;
        if (sp < 1) return done(2);
        if (olen + 1 > 65536) return done(11);
        out[olen++] = D[--sp] & 255;
        pc++;
        break;
      case 0x52: // IN
        steps++;
        if (sp + 1 > 256) return done(3);
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        pc++;
        break;
      case 0x53: // EXIT
        steps++;
        if (sp < 1) return done(2);
        return done(D[--sp] & 255);
      default: // unknown opcode
        return done(5);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const [out, code] = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), `${code}\n`);
}
