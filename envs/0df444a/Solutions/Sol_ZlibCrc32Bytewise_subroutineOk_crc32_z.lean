-- Prove2me | solution 1 for ZlibCrc32Bytewise.subroutineOk_crc32_z
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T01:55:22.179808+00:00
-- url     : https://prove2.me/submissions/26b2674b-d326-482e-a0bf-5e316dcb75e5

import Mathlib.Tactic.IntervalCases
import Definitions.Def_ZlibCrc32Bytewise_Spec

section
/-! # Instruction fetch for the placed `zlibCrc32` text block -/

namespace ZlibCrc32Bytewise.Proof

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-- The placed program the goal talks about. -/
def prog (pl : Placement) : Program := zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)

theorem length_bytesOfWordLE (w : BitVec 32) : (bytesOfWordLE w).length = 4 := by
  simp [bytesOfWordLE, bytesLE]

theorem drop_take_flatMap_bytesOfWordLE {α : Type} (g : α → BitVec 32) :
    ∀ (L : List α) (j : Nat) (hj : j < L.length),
      ((L.flatMap fun a => bytesOfWordLE (g a)).drop (4 * j)).take 4 =
        bytesOfWordLE (g (L[j]'hj))
  | [], _, hj => by simp at hj
  | a :: L, 0, _ => by
    simp only [List.flatMap_cons, Nat.mul_zero, List.drop_zero, List.getElem_cons_zero]
    rw [List.take_append_of_le_length (by simp [length_bytesOfWordLE])]
    exact List.take_of_length_le (by simp [length_bytesOfWordLE])
  | a :: L, j + 1, hj => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [show 4 * (j + 1) = (bytesOfWordLE (g a)).length + 4 * j by
          simp [length_bytesOfWordLE]; omega,
      ← List.drop_drop, List.drop_left]
    exact drop_take_flatMap_bytesOfWordLE g L j (by simp at hj; omega)

theorem take4_drop_patched {blk : CodeBlock} {pl : Placement} {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ blk.code.length) :
    ((blk.patched pl).drop off).take 4 = bytesOfWordLE (blk.patchedWord pl off) := by
  have hj : off / 4 < (List.range (blk.code.length / 4)).length := by
    simp only [List.length_range]; omega
  have h := drop_take_flatMap_bytesOfWordLE (fun j => blk.patchedWord pl (4 * j))
    (List.range (blk.code.length / 4)) (off / 4) hj
  rw [List.getElem_range, show 4 * (off / 4) = off by omega] at h
  exact h

theorem codeLoaded_cell {p : Program} {m : Memory} (h : p.CodeLoaded m) (i : Nat)
    (hi : i < p.code.length) :
    m.read8 (p.base + BitVec.ofNat 64 i) = p.code[i] ∧
    m.perm (p.base + BitVec.ofNat 64 i) = some Perm.rx := by
  unfold Program.CodeLoaded at h
  exact ⟨(h.2.2 i hi).1, (h.2.2 i hi).2.1⟩

set_option maxRecDepth 100000 in
theorem code_length : zlibCrc32PlacedCode.length = 1056 := by rfl

theorem patched_length (pl : Placement) : (zlibCrc32Text.patched pl).length = 1056 := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE]
  show (List.map (fun _ => 4) (List.range (zlibCrc32PlacedCode.length / 4))).sum = 1056
  rw [code_length]; rfl

theorem hook_none (pl : Placement) (pc : BitVec 64) : (prog pl).externAt? pc = none := by
  simp [prog, Program.externAt?, Program.hookAtOff?, PlacedLib.program, zlibCrc32Lib, zlibCrc32Text]

/-- Byte `k < 4` of the word at aligned offset `off` of the placed code. -/
theorem read8_code {pl : Placement} {m : Memory} (hCL : (prog pl).CodeLoaded m) {off k : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 1056) (hk : k < 4) :
    m.read8 (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      (zlibCrc32Text.patchedWord pl off).extractLsb' (8 * k) 8 ∧
    m.perm (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
  have hl : (prog pl).code.length = 1056 := patched_length pl
  have h := codeLoaded_cell hCL (off + k) (by omega)
  have ha : pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
      (prog pl).base + BitVec.ofNat 64 (off + k) := by
    show _ = pl.base + _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [ha]
  refine ⟨?_, h.2⟩
  rw [h.1]
  have ht := take4_drop_patched (blk := zlibCrc32Text) (pl := pl) hal
    (by rw [show zlibCrc32Text.code = zlibCrc32PlacedCode from rfl, code_length]; exact hlen)
  have e1 : (prog pl).code[off + k]'(by omega) =
      (((zlibCrc32Text.patched pl).drop off).take 4)[k]'(by
        simp [List.length_take, List.length_drop, patched_length]; omega) := by
    simp only [List.getElem_take, List.getElem_drop]; rfl
  rw [e1]
  simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * k + i < 32 := by omega
  simp [hi, this]; omega

theorem fetch_word {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded m) {off : Nat} (hal : off % 4 = 0) (hlen : off + 4 ≤ 1056) :
    (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      decode (zlibCrc32Text.patchedWord pl off) := by
  have hb4 : pl.base.toNat % 4 = 0 := by
    have := hP.text.base_aligned; simpa [zlibCrc32Lib, zlibCrc32Text] using this
  have hnw : pl.base.toNat + 1056 ≤ 2 ^ 64 := by
    have := hP.text.no_wrap
    have hl : zlibCrc32Text.code.length = 1056 := code_length
    rw [show zlibCrc32Lib.text = zlibCrc32Text from rfl, hl] at this
    exact this
  have hpc : (pl.base + BitVec.ofNat 64 off).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : off % 2 ^ 64 = off := Nat.mod_eq_of_lt (by omega)
    have h2 : (pl.base.toNat + off) % 2 ^ 64 = pl.base.toNat + off := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]; omega
  have r0 := read8_code hCL hal hlen (k := 0) (by omega)
  have r1 := read8_code hCL hal hlen (k := 1) (by omega)
  have r2 := read8_code hCL hal hlen (k := 2) (by omega)
  have r3 := read8_code hCL hal hlen (k := 3) (by omega)
  simp only [Program.fetchMem, hook_none, Option.isSome_none, Bool.false_eq_true, if_false, hpc,
    ne_eq, not_true_eq_false]
  generalize ha : pl.base + BitVec.ofNat 64 off = a at *
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at r0 r1 r2 r3
  have hx : m.canExec a 4 = true := by
    simp only [Memory.canExec, Memory.allPerm, BitVec.add_assoc, BitVec.reduceAdd]
    simp only [BitVec.add_zero] at r0
    simp [r0.2, r1.2, r2.2, r3.2, Perm.rx]
  simp only [hx, Bool.not_true, Bool.false_eq_true, if_false]
  congr 1
  simp only [Memory.read32]
  rw [r0.1, r1.1, r2.1, r3.1]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

end ZlibCrc32Bytewise.Proof
end

section
/-! # The instructions of `crc32_z` at each (unrelocated) address -/

namespace ZlibCrc32Bytewise.Proof

open Arm64 Arm64.Obj

set_option maxRecDepth 100000

def iCbzX1 : Instr := .cbz .W64 false (.gpr 1#5) 0x100#64
def iCmp8 : Instr := .addSubImm .W64 .SUBS .xzr (.gpr 2#5) 8#12 false
def iMvn : Instr := .logicalShift .W32 .ORN (.gpr 9#5) .xzr (.gpr 0#5) .LSL 0
def iBlo : Instr := .bCond .CC 0xc4#64
def iLdrb (k : BitVec 64) : Instr := .ldr .W32 .B8 false (.gpr 10#5) (.Offset (.gpr 1#5) k)
def iSub8 : Instr := .addSubImm .W64 .SUB (.gpr 2#5) (.gpr 2#5) 8#12 false
def iCmp7 : Instr := .addSubImm .W64 .SUBS .xzr (.gpr 2#5) 7#12 false
def iEorW : Instr := .logicalShift .W32 .EOR (.gpr 10#5) (.gpr 10#5) (.gpr 9#5) .LSL 0
def iAnd : Instr := .logicalImm .W64 .AND (.gpr 10#5) (.gpr 10#5) 0xff#64
def iLdrT (rt : BitVec 5) : Instr :=
  .ldr .W32 .W32 false (.gpr rt) (.RegOffset (.gpr 8#5) (.gpr 10#5) .UXTX 2)
def iEorX (rn : BitVec 5) : Instr := .logicalShift .W64 .EOR (.gpr 9#5) (.gpr rn) (.gpr 9#5) .LSR 8
def iAdd8 : Instr := .addSubImm .W64 .ADD (.gpr 10#5) (.gpr 1#5) 8#12 false
def iMovX1 : Instr := .logicalShift .W64 .ORR (.gpr 1#5) .xzr (.gpr 10#5) .LSL 0
def iBhi : Instr := .bCond .HI 0xffffffffffffff50#64
def iCbzX2 : Instr := .cbz .W64 false (.gpr 2#5) 0x28#64
def iLdrbPost : Instr := .ldr .W32 .B8 false (.gpr 10#5) (.PostIndex (.gpr 1#5) 1#64)
def iSubs1 : Instr := .addSubImm .W64 .SUBS (.gpr 2#5) (.gpr 2#5) 1#12 false
def iBne : Instr := .bCond .NE 0xffffffffffffffe8#64
def iEorFin : Instr := .logicalImm .W64 .EOR (.gpr 0#5) (.gpr 9#5) 0xffffffff#64
def iRet : Instr := .ret (.gpr 30#5)

theorem patchedWord_plain (pl : Placement) {off : Nat} (h : zlibCrc32Text.relocAt? off = none) :
    zlibCrc32Text.patchedWord pl off = zlibCrc32Text.wordAt off := by
  simp [CodeBlock.patchedWord, h]

section
variable {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl)
  (hCL : (prog pl).CodeLoaded m)
include hP hCL


theorem f_00 : (prog pl).fetchMem m (pl.base + 12#64) = some (iCbzX1) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_04 : (prog pl).fetchMem m (pl.base + 16#64) = some (iCmp8) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_08 : (prog pl).fetchMem m (pl.base + 20#64) = some (iMvn) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_0c : (prog pl).fetchMem m (pl.base + 24#64) = some (iBlo) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_18 : (prog pl).fetchMem m (pl.base + 36#64) = some (iLdrb 0#64) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1c : (prog pl).fetchMem m (pl.base + 40#64) = some (iSub8) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_20 : (prog pl).fetchMem m (pl.base + 44#64) = some (iCmp7) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_24 : (prog pl).fetchMem m (pl.base + 48#64) = some (iEorW) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_28 : (prog pl).fetchMem m (pl.base + 52#64) = some (iAnd) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_2c : (prog pl).fetchMem m (pl.base + 56#64) = some (iLdrT 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_30 : (prog pl).fetchMem m (pl.base + 60#64) = some (iEorX 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_34 : (prog pl).fetchMem m (pl.base + 64#64) = some (iLdrb 1#64) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_38 : (prog pl).fetchMem m (pl.base + 68#64) = some (iEorW) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_3c : (prog pl).fetchMem m (pl.base + 72#64) = some (iAnd) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_40 : (prog pl).fetchMem m (pl.base + 76#64) = some (iLdrT 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_44 : (prog pl).fetchMem m (pl.base + 80#64) = some (iEorX 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_48 : (prog pl).fetchMem m (pl.base + 84#64) = some (iLdrb 2#64) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_4c : (prog pl).fetchMem m (pl.base + 88#64) = some (iEorW) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_50 : (prog pl).fetchMem m (pl.base + 92#64) = some (iAnd) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_54 : (prog pl).fetchMem m (pl.base + 96#64) = some (iLdrT 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_58 : (prog pl).fetchMem m (pl.base + 100#64) = some (iEorX 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_5c : (prog pl).fetchMem m (pl.base + 104#64) = some (iLdrb 3#64) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_60 : (prog pl).fetchMem m (pl.base + 108#64) = some (iEorW) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_64 : (prog pl).fetchMem m (pl.base + 112#64) = some (iAnd) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_68 : (prog pl).fetchMem m (pl.base + 116#64) = some (iLdrT 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_6c : (prog pl).fetchMem m (pl.base + 120#64) = some (iEorX 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_70 : (prog pl).fetchMem m (pl.base + 124#64) = some (iLdrb 4#64) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_74 : (prog pl).fetchMem m (pl.base + 128#64) = some (iEorW) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_78 : (prog pl).fetchMem m (pl.base + 132#64) = some (iAnd) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_7c : (prog pl).fetchMem m (pl.base + 136#64) = some (iLdrT 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_80 : (prog pl).fetchMem m (pl.base + 140#64) = some (iEorX 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_84 : (prog pl).fetchMem m (pl.base + 144#64) = some (iLdrb 5#64) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_88 : (prog pl).fetchMem m (pl.base + 148#64) = some (iEorW) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_8c : (prog pl).fetchMem m (pl.base + 152#64) = some (iAnd) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_90 : (prog pl).fetchMem m (pl.base + 156#64) = some (iLdrT 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_94 : (prog pl).fetchMem m (pl.base + 160#64) = some (iEorX 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_98 : (prog pl).fetchMem m (pl.base + 164#64) = some (iLdrb 6#64) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_9c : (prog pl).fetchMem m (pl.base + 168#64) = some (iEorW) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a0 : (prog pl).fetchMem m (pl.base + 172#64) = some (iAnd) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a4 : (prog pl).fetchMem m (pl.base + 176#64) = some (iLdrT 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a8 : (prog pl).fetchMem m (pl.base + 180#64) = some (iEorX 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_ac : (prog pl).fetchMem m (pl.base + 184#64) = some (iLdrb 7#64) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b0 : (prog pl).fetchMem m (pl.base + 188#64) = some (iEorW) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b4 : (prog pl).fetchMem m (pl.base + 192#64) = some (iAnd) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b8 : (prog pl).fetchMem m (pl.base + 196#64) = some (iLdrT 11#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_bc : (prog pl).fetchMem m (pl.base + 200#64) = some (iAdd8) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c0 : (prog pl).fetchMem m (pl.base + 204#64) = some (iMovX1) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c4 : (prog pl).fetchMem m (pl.base + 208#64) = some (iEorX 11#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c8 : (prog pl).fetchMem m (pl.base + 212#64) = some (iBhi) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_cc : (prog pl).fetchMem m (pl.base + 216#64) = some (iMovX1) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d0 : (prog pl).fetchMem m (pl.base + 220#64) = some (iCbzX2) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_dc : (prog pl).fetchMem m (pl.base + 232#64) = some (iLdrbPost) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e0 : (prog pl).fetchMem m (pl.base + 236#64) = some (iSubs1) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e4 : (prog pl).fetchMem m (pl.base + 240#64) = some (iEorW) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e8 : (prog pl).fetchMem m (pl.base + 244#64) = some (iAnd) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_ec : (prog pl).fetchMem m (pl.base + 248#64) = some (iLdrT 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f0 : (prog pl).fetchMem m (pl.base + 252#64) = some (iEorX 10#5) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f4 : (prog pl).fetchMem m (pl.base + 256#64) = some (iBne) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f8 : (prog pl).fetchMem m (pl.base + 260#64) = some (iEorFin) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_fc : (prog pl).fetchMem m (pl.base + 264#64) = some (iRet) := by
  rw [fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

end

end ZlibCrc32Bytewise.Proof
end

section
/-! # Abstract machine states and single-step lemmas

Every state reached by `crc32_z` is `mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps`: the entry state `s0`
with only the clobbered registers, `pc` and the flags replaced. -/

namespace ZlibCrc32Bytewise.Proof

open Arm64 Arm64.Obj

set_option maxRecDepth 100000

/-- The register file of `s0` with `x0, x1, x2, x8, x9, x10, x11` replaced. -/
def mkRegs (r : RegFile) (x0 x1 x2 x8 x9 x10 x11 : BitVec 64) : RegFile :=
  ⟨fun i => if i = 0#5 then x0 else if i = 1#5 then x1 else if i = 2#5 then x2 else
    if i = 8#5 then x8 else if i = 9#5 then x9 else if i = 10#5 then x10 else
    if i = 11#5 then x11 else r.regs i⟩

/-- The abstract state. -/
def mkS (s0 : State) (pc x0 x1 x2 x8 x9 x10 x11 : BitVec 64) (ps : PState) : State :=
  { s0 with regs := mkRegs s0.regs x0 x1 x2 x8 x9 x10 x11, pc := pc, pstate := ps }

section lemmas
variable (s0 : State) (pc x0 x1 x2 x8 x9 x10 x11 : BitVec 64) (ps : PState)

@[simp] theorem mkS_mem : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).mem = s0.mem := rfl
@[simp] theorem mkS_pc : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).pc = pc := rfl
@[simp] theorem mkS_sp : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).sp = s0.sp := rfl
@[simp] theorem mkS_status : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).status = s0.status := rfl
@[simp] theorem mkS_pstate : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).pstate = ps := rfl
@[simp] theorem mkS_vregs : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).vregs = s0.vregs := rfl

@[simp] theorem rd_x0 : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).readReg64 (.gpr 0#5) = x0 := rfl
@[simp] theorem rd_x1 : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).readReg64 (.gpr 1#5) = x1 := rfl
@[simp] theorem rd_x2 : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).readReg64 (.gpr 2#5) = x2 := rfl
@[simp] theorem rd_x8 : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).readReg64 (.gpr 8#5) = x8 := rfl
@[simp] theorem rd_x9 : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).readReg64 (.gpr 9#5) = x9 := rfl
@[simp] theorem rd_x10 : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).readReg64 (.gpr 10#5) = x10 := rfl
@[simp] theorem rd_x11 : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).readReg64 (.gpr 11#5) = x11 := rfl
@[simp] theorem rd_x30 : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).readReg64 (.gpr 30#5) =
    s0.readReg64 (.gpr 30#5) := rfl
@[simp] theorem rd_xzr : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).readReg64 .xzr = 0#64 := rfl

@[simp] theorem wr_x0 (v : BitVec 64) : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).writeReg64 (.gpr 0#5) v =
    mkS s0 pc v x1 x2 x8 x9 x10 x11 ps := by
  simp only [mkS, State.writeReg64, mkRegs, RegFile.write]; rw [if_neg (by decide)]
  congr 2; funext i; split <;> simp_all
@[simp] theorem wr_x1 (v : BitVec 64) : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).writeReg64 (.gpr 1#5) v =
    mkS s0 pc x0 v x2 x8 x9 x10 x11 ps := by
  simp only [mkS, State.writeReg64, mkRegs, RegFile.write]; rw [if_neg (by decide)]
  congr 2; funext i; split <;> simp_all
@[simp] theorem wr_x2 (v : BitVec 64) : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).writeReg64 (.gpr 2#5) v =
    mkS s0 pc x0 x1 v x8 x9 x10 x11 ps := by
  simp only [mkS, State.writeReg64, mkRegs, RegFile.write]; rw [if_neg (by decide)]
  congr 2; funext i; split <;> simp_all
@[simp] theorem wr_x8 (v : BitVec 64) : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).writeReg64 (.gpr 8#5) v =
    mkS s0 pc x0 x1 x2 v x9 x10 x11 ps := by
  simp only [mkS, State.writeReg64, mkRegs, RegFile.write]; rw [if_neg (by decide)]
  congr 2; funext i; split <;> simp_all
@[simp] theorem wr_x9 (v : BitVec 64) : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).writeReg64 (.gpr 9#5) v =
    mkS s0 pc x0 x1 x2 x8 v x10 x11 ps := by
  simp only [mkS, State.writeReg64, mkRegs, RegFile.write]; rw [if_neg (by decide)]
  congr 2; funext i; split <;> simp_all
@[simp] theorem wr_x10 (v : BitVec 64) : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).writeReg64 (.gpr 10#5) v =
    mkS s0 pc x0 x1 x2 x8 x9 v x11 ps := by
  simp only [mkS, State.writeReg64, mkRegs, RegFile.write]; rw [if_neg (by decide)]
  congr 2; funext i; split <;> simp_all
@[simp] theorem wr_x11 (v : BitVec 64) : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).writeReg64 (.gpr 11#5) v =
    mkS s0 pc x0 x1 x2 x8 x9 x10 v ps := by
  simp only [mkS, State.writeReg64, mkRegs, RegFile.write]; rw [if_neg (by decide)]
  congr 2; funext i; split <;> simp_all
@[simp] theorem wr_xzr (v : BitVec 64) : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).writeReg64 .xzr v =
    mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps := rfl
@[simp] theorem mkS_advancePC : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).advancePC =
    mkS s0 (pc + 4#64) x0 x1 x2 x8 x9 x10 x11 ps := rfl
@[simp] theorem mkS_setPC (q : BitVec 64) : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).setPC q =
    mkS s0 q x0 x1 x2 x8 x9 x10 x11 ps := rfl
@[simp] theorem mkS_setPState (q : PState) : (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps).setPState q =
    mkS s0 pc x0 x1 x2 x8 x9 x10 x11 q := rfl

end lemmas

/-! ## Steps utilities -/

theorem Steps.trans' {p : Program} {a b c : State} (h1 : Steps p a b) (h2 : Steps p b c) :
    Steps p a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact Steps.step h (ih h2)

theorem Steps.one {p : Program} {a b : State} (h : Step p a b) : Steps p a b :=
  Steps.step h (Steps.refl _)

/-- Executing a fetched instruction from an abstract state. -/
theorem step_of {pl : Placement} {s : State} {inst : Instr} (hrun : s.status = .Running)
    (hf : (prog pl).fetchMem s.mem s.pc = some inst) {s' : State}
    (he : execInstWithSvc (evalSvc Syscall.standard) inst s = s') : Step (prog pl) s s' := by
  have := Step.exec (prog := prog pl) hrun hf
  rw [Program.evalInst] at this
  rwa [show (prog pl).svc = Syscall.standard from rfl, he] at this

theorem step_mkS {pl : Placement} {s0 : State} {pc x0 x1 x2 x8 x9 x10 x11 : BitVec 64}
    {ps : PState} {inst : Instr} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem s0.mem pc = some inst) {s' : State}
    (he : execInstWithSvc (evalSvc Syscall.standard) inst (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps) = s') :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps) s' :=
  step_of (pl := pl) (s := mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps) hrun hf he

end ZlibCrc32Bytewise.Proof
end

section
/-! # Single-step lemmas for each instruction of `crc32_z` on abstract states -/
namespace ZlibCrc32Bytewise.Proof
open Arm64 Arm64.Obj


section
variable (svc : State → State) (s : State)
theorem ex_cbz (w : RegWidth) (nz : Bool) (rt : Reg) (off : BitVec 64) :
    execInstWithSvc svc (.cbz w nz rt off) s =
      (let val := s.readReg w rt
       let cond := if nz then (val == 0#64) != true else val == 0#64
       if cond then s.setPC (s.pc + off) else s.advancePC) := rfl
theorem ex_addSubImm (w : RegWidth) (op : AddSubOp) (rd rn : Reg) (imm : BitVec 12) (sh : Bool) :
    execInstWithSvc svc (.addSubImm w op rd rn imm sh) s = execAddSubImm w op rd rn imm sh s := rfl
theorem ex_logicalShift (w : RegWidth) (op : LogicalOp) (rd rn rm : Reg) (sh : ShiftType) (a : Nat) :
    execInstWithSvc svc (.logicalShift w op rd rn rm sh a) s = execLogicalShift w op rd rn rm sh a s := rfl
theorem ex_logicalImm (w : RegWidth) (op : LogicalOp) (rd rn : Reg) (mask : BitVec 64) :
    execInstWithSvc svc (.logicalImm w op rd rn mask) s = execLogicalImm w op rd rn mask s := rfl
theorem ex_bCond (c : CondCode) (off : BitVec 64) :
    execInstWithSvc svc (.bCond c off) s =
      if ConditionHolds c s.pstate then s.setPC (s.pc + off) else s.advancePC := rfl
theorem ex_ldr (w : RegWidth) (sz : MemWidth) (sg : Bool) (rt : Reg) (a : AddrMode) :
    execInstWithSvc svc (.ldr w sz sg rt a) s = execLdr w sz sg rt a s := rfl
theorem ex_adr (pg : Bool) (rd : Reg) (off : BitVec 64) :
    execInstWithSvc svc (.adr pg rd off) s =
      (s.writeReg64 rd ((if pg then s.pc &&& 0xfffffffffffff000#64 else s.pc) + off)).advancePC := rfl
theorem ex_nop : execInstWithSvc svc .nop s = s.advancePC := rfl
theorem ex_ret (rn : Reg) : execInstWithSvc svc (.ret rn) s = s.setPC (s.readReg64 rn) := rfl
end

variable {pl : Placement} {s0 : State} {pc x0 x1 x2 x8 x9 x10 x11 : BitVec 64} {ps : PState}

def subFlags (x y : BitVec 64) : PState := (AddWithCarry64 x (~~~y) true).2

theorem awc_fst (x y : BitVec 64) : (AddWithCarry64 x y true).1 = x + y + 1#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]
  omega

theorem awc_sub1 (x : BitVec 64) : (AddWithCarry64 x 18446744073709551614#64 true).1 = x - 1#64 := by
  rw [awc_fst]; bv_omega

theorem s_cbzX1 (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some iCbzX1)
    (h1 : x1 ≠ 0#64) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps) (mkS s0 (pc + 4#64) x0 x1 x2 x8 x9 x10 x11 ps) :=
  step_mkS hrun hf (by rw [iCbzX1, ex_cbz]; simp [State.readReg, h1])

theorem s_cmp8 (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some iCmp8) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 x1 x2 x8 x9 x10 x11 (subFlags x2 8#64)) :=
  step_mkS hrun hf (by rw [iCmp8, ex_addSubImm]; simp [State.readReg, State.writeReg, evalAddSub, subFlags])

theorem s_mvn (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some iMvn) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 x1 x2 x8 ((~~~ (x0.truncate 32)).zeroExtend 64) x10 x11 ps) :=
  step_mkS hrun hf (by rw [iMvn, ex_logicalShift]; simp [State.readReg, State.writeReg, evalLogical, shiftVal, shift32, State.readReg32])

theorem s_bCond_t {c : CondCode} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem s0.mem pc = some (.bCond c off)) (hc : ConditionHolds c ps = true) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps) (mkS s0 (pc + off) x0 x1 x2 x8 x9 x10 x11 ps) :=
  step_mkS hrun hf (by rw [ex_bCond]; simp [hc])

theorem s_bCond_f {c : CondCode} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem s0.mem pc = some (.bCond c off)) (hc : ConditionHolds c ps = false) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps) (mkS s0 (pc + 4#64) x0 x1 x2 x8 x9 x10 x11 ps) :=
  step_mkS hrun hf (by rw [ex_bCond]; simp [hc])

theorem s_ldrb {k : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem s0.mem pc = some (iLdrb k)) (hr : s0.mem.canRead (x1 + k) 1 = true) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 x1 x2 x8 x9 ((s0.mem.read8 (x1 + k)).zeroExtend 64) x11 ps) :=
  step_mkS hrun hf (by
    rw [iLdrb, ex_ldr]
    simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, hr,
      Memory.readSized, State.writeReg])

theorem s_sub8 (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some iSub8) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 x1 (x2 - 8#64) x8 x9 x10 x11 ps) :=
  step_mkS hrun hf (by
    rw [iSub8, ex_addSubImm]; simp [State.readReg, State.writeReg, evalAddSub, AddWithCarry64]
    congr 1; apply BitVec.eq_of_toNat_eq; simp; omega)

theorem s_cmp7 (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some iCmp7) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 x1 x2 x8 x9 x10 x11 (subFlags x2 7#64)) :=
  step_mkS hrun hf (by rw [iCmp7, ex_addSubImm]; simp [State.readReg, State.writeReg, evalAddSub, subFlags])

theorem s_eorW (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some iEorW) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 x1 x2 x8 x9 ((x10.truncate 32 ^^^ x9.truncate 32).zeroExtend 64) x11 ps) :=
  step_mkS hrun hf (by
    rw [iEorW, ex_logicalShift]
    simp [State.readReg, State.writeReg, evalLogical, shiftVal, shift32, State.readReg32])

theorem s_and (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some iAnd) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 x1 x2 x8 x9 (x10 &&& 0xff#64) x11 ps) :=
  step_mkS hrun hf (by rw [iAnd, ex_logicalImm]; simp [State.readReg, State.writeReg, evalLogical])

theorem s_ldrT10 (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some (iLdrT 10#5))
    (hr : s0.mem.canRead (x8 + (x10 <<< 2)) 4 = true) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 x1 x2 x8 x9 ((s0.mem.read32 (x8 + (x10 <<< 2))).zeroExtend 64) x11 ps) :=
  step_mkS hrun hf (by
    rw [iLdrT, ex_ldr]
    simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, extendVal, hr,
      Memory.readSized, State.writeReg])

theorem s_ldrT11 (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some (iLdrT 11#5))
    (hr : s0.mem.canRead (x8 + (x10 <<< 2)) 4 = true) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 x1 x2 x8 x9 x10 ((s0.mem.read32 (x8 + (x10 <<< 2))).zeroExtend 64) ps) :=
  step_mkS hrun hf (by
    rw [iLdrT, ex_ldr]
    simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, extendVal, hr,
      Memory.readSized, State.writeReg])

theorem s_eorX10 (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some (iEorX 10#5)) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 x1 x2 x8 (x10 ^^^ (x9 >>> 8)) x10 x11 ps) :=
  step_mkS hrun hf (by
    rw [iEorX, ex_logicalShift]; simp [State.readReg, State.writeReg, evalLogical, shiftVal, shift64])

theorem s_eorX11 (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some (iEorX 11#5)) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 x1 x2 x8 (x11 ^^^ (x9 >>> 8)) x10 x11 ps) :=
  step_mkS hrun hf (by
    rw [iEorX, ex_logicalShift]; simp [State.readReg, State.writeReg, evalLogical, shiftVal, shift64])

theorem s_add8 (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some iAdd8) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 x1 x2 x8 x9 (x1 + 8#64) x11 ps) :=
  step_mkS hrun hf (by
    rw [iAdd8, ex_addSubImm]; simp [State.readReg, State.writeReg, evalAddSub, AddWithCarry64]
    congr 1; apply BitVec.eq_of_toNat_eq; simp; omega)

theorem s_movX1 (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some iMovX1) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 x10 x2 x8 x9 x10 x11 ps) :=
  step_mkS hrun hf (by
    rw [iMovX1, ex_logicalShift]; simp [State.readReg, State.writeReg, evalLogical, shiftVal, shift64])

theorem s_cbzX2_t (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some iCbzX2) :
    Step (prog pl) (mkS s0 pc x0 x1 0#64 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 0x28#64) x0 x1 0#64 x8 x9 x10 x11 ps) :=
  step_mkS hrun hf (by rw [iCbzX2, ex_cbz]; simp [State.readReg])

theorem s_cbzX2_f (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some iCbzX2)
    (h2 : x2 ≠ 0#64) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 x1 x2 x8 x9 x10 x11 ps) :=
  step_mkS hrun hf (by rw [iCbzX2, ex_cbz]; simp [State.readReg, h2])

theorem s_ldrbPost (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem s0.mem pc = some iLdrbPost) (hr : s0.mem.canRead x1 1 = true) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 (x1 + 1#64) x2 x8 x9 ((s0.mem.read8 x1).zeroExtend 64) x11 ps) :=
  step_mkS hrun hf (by
    rw [iLdrbPost, ex_ldr]
    simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, hr,
      Memory.readSized, State.writeReg])

theorem s_subs1 (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some iSubs1) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) x0 x1 (x2 - 1#64) x8 x9 x10 x11 (subFlags x2 1#64)) :=
  step_mkS hrun hf (by
    rw [iSubs1, ex_addSubImm]; simp [State.readReg, State.writeReg, evalAddSub, subFlags, awc_sub1])

theorem s_eorFin (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some iEorFin) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pc + 4#64) (x9 ^^^ 0xffffffff#64) x1 x2 x8 x9 x10 x11 ps) :=
  step_mkS hrun hf (by rw [iEorFin, ex_logicalImm]; simp [State.readReg, State.writeReg, evalLogical])

theorem s_ret (hrun : s0.status = .Running) (hf : (prog pl).fetchMem s0.mem pc = some iRet) :
    Step (prog pl) (mkS s0 pc x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (s0.readReg64 (.gpr 30#5)) x0 x1 x2 x8 x9 x10 x11 ps) :=
  step_mkS hrun hf (by rw [iRet, ex_ret]; simp)

end ZlibCrc32Bytewise.Proof
end

section
/-! # The relocated `ADRP x8, crc_table` + `ADD x8, x8, :lo12:crc_table` pairs

Symbolic decoding of the relocated words (any placement), in both the unrelaxed form and the
linker-relaxed `NOP` + `ADR` form. -/

namespace ZlibCrc32Bytewise.Proof

open Arm64 Arm64.Obj

set_option maxRecDepth 100000

abbrev tsym : String := "crc_table [zlib_crc32]"

theorem pw_adrp (pl : Placement) (o : Nat) (ho : o = 28 ∨ o = 224) :
    zlibCrc32Text.patchedWord pl o =
      if pl.relax o then nopWord else adrpWord 0x90000008#32 (pl.base + BitVec.ofNat 64 o) (pl.ρ tsym) := by
  have hr : zlibCrc32Text.relocAt? o = some { off := o, kind := .adrpHi21, sym := tsym } := by
    rcases ho with rfl | rfl <;> rfl
  have h1 : zlibCrc32Text.relaxableAt o = true := by rcases ho with rfl | rfl <;> decide
  have h2 : zlibCrc32Text.relaxableAt (o - 4) = false := by rcases ho with rfl | rfl <;> decide
  have hw : zlibCrc32Text.wordAt o = 0x90000008#32 := by rcases ho with rfl | rfl <;> rfl
  have hlk : lookup tsym zlibCrc32Text.symbols = none := by decide
  have h4 : (4 ≤ o) = True := by rcases ho with rfl | rfl <;> simp
  cases h : pl.relax o <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h2, hr, hw, h4,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, CodeBlock.target,
      CodeBlock.resolve, hlk, addSignedAddr, patchRelocWord, RelocKind.isGotOrTlsIe]

theorem pw_add (pl : Placement) (o : Nat) (ho : o = 28 ∨ o = 224) :
    zlibCrc32Text.patchedWord pl (o + 4) =
      if pl.relax o then adrWord (adrTemplate 0x91000108#32) (pl.base + BitVec.ofNat 64 (o + 4)) (pl.ρ tsym)
      else lo12Word 0 0x91000108#32 (pl.ρ tsym) := by
  have hr : zlibCrc32Text.relocAt? (o + 4) = some { off := o + 4, kind := .addLo12, sym := tsym } := by
    rcases ho with rfl | rfl <;> rfl
  have h1 : zlibCrc32Text.relaxableAt o = true := by rcases ho with rfl | rfl <;> decide
  have h2 : zlibCrc32Text.relaxableAt (o + 4) = false := by rcases ho with rfl | rfl <;> decide
  have hw : zlibCrc32Text.wordAt (o + 4) = 0x91000108#32 := by rcases ho with rfl | rfl <;> rfl
  have hlk : lookup tsym zlibCrc32Text.symbols = none := by decide
  have h4 : (4 ≤ o + 4) = True := by simp
  cases h : pl.relax o <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h2, hr, hw, h4,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, CodeBlock.target,
      CodeBlock.resolve, hlk, addSignedAddr, patchRelocWord, RelocKind.isGotOrTlsIe]

theorem beq_false_of_mask {w K A M C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A &&& M) :
    (w &&& M == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, ← hK, BitVec.and_assoc, BitVec.and_comm M K, ← BitVec.and_assoc]

theorem beq_false_of_mask' {w K A C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A) :
    (w == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, hK]

theorem decode_adr_class (w : BitVec 32) (hK : w &&& 0x1f000000#32 = 0x10000000#32) :
    decode w = some (.adr (w.getLsbD 31) (Reg.fromZRBits (w.extractLsb' 0 5))
      (if w.getLsbD 31 then ((w.extractLsb' 5 19 ++ w.extractLsb' 29 2).signExtend 64) <<< 12
       else (w.extractLsb' 5 19 ++ w.extractLsb' 29 2).signExtend 64)) := by
  rw [decode]
  simp only [beq_false_of_mask' hK (C := 0xd503201f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4000001#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4200000#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd503201f#32) (M := 0xfffff01f#32) (by decide),
    beq_false_of_mask hK (C := 0#32) (M := 0xffff0000#32) (by decide),
    beq_false_of_mask hK (C := 0xd50b7420#32) (M := 0xffffffe0#32) (by decide), hK]
  simp

theorem decode_addimm_class (w : BitVec 32) (hK : w &&& 0x1f800000#32 = 0x11000000#32) :
    decode w = some (
      let op := AddSubOp.ofBits (w.getLsbD 30) (w.getLsbD 29)
      .addSubImm (RegWidth.ofBool (w.getLsbD 31)) op
        (if op.setsFlags then Reg.fromZRBits (w.extractLsb' 0 5) else Reg.fromSPBits (w.extractLsb' 0 5))
        (Reg.fromSPBits (w.extractLsb' 5 5)) (w.extractLsb' 10 12) (w.getLsbD 22)) := by
  rw [decode]
  simp only [beq_false_of_mask' hK (C := 0xd503201f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4000001#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4200000#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd503201f#32) (M := 0xfffff01f#32) (by decide),
    beq_false_of_mask hK (C := 0#32) (M := 0xffff0000#32) (by decide),
    beq_false_of_mask hK (C := 0xd50b7420#32) (M := 0xffffffe0#32) (by decide),
    beq_false_of_mask hK (C := 0x10000000#32) (M := 0x1f000000#32) (by decide), hK]
  simp

theorem hi_bits32 (D : BitVec 64) (h1 : -(2^32:Int) ≤ D.toInt) (h2 : D.toInt < 2^32) :
    ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  interval_cases i <;> (try simp only [decide_eq_decide]) <;> (try split at h1) <;> omega

theorem hi_bits20 (D : BitVec 64) (h1 : -(2^20:Int) ≤ D.toInt) (h2 : D.toInt < 2^20) :
    ∀ i, 20 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 20 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  interval_cases i <;> (try simp only [decide_eq_decide]) <;> (try split at h1) <;> omega

theorem pageOf_eq (x : BitVec 64) : pageOf x = (x >>> 12) <<< 12 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [pageOf, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem pageOf_toNat (x : BitVec 64) : (pageOf x).toNat = x.toNat / 4096 * 4096 := by
  rw [pageOf_eq]; simp [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]; omega

theorem lo_bits (a b : BitVec 64) : ∀ i, i < 12 → (pageOf a - pageOf b).getLsbD i = false := by
  intro i hi
  have h : (pageOf a - pageOf b).toNat % 4096 = 0 := by
    rw [BitVec.toNat_sub, pageOf_toNat, pageOf_toNat]
    have := a.isLt; have := b.isLt; omega
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  generalize (pageOf a - pageOf b).toNat = n at h ⊢
  interval_cases i <;> simp <;> omega

theorem page_add_lo (T : BitVec 64) : pageOf T + (T.extractLsb' 0 12).setWidth 64 = T := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, pageOf_toNat]
  simp [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat]
  have := T.isLt; omega


section words
variable (D : BitVec 64)

theorem wA_mask : adrpWordOff 0x90000008#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_31 : (adrpWordOff 0x90000008#32 D).getLsbD 31 = true := by
  simp [adrpWordOff]

theorem wA_rd : (adrpWordOff 0x90000008#32 D).extractLsb' 0 5 = 8#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_off (hlo : ∀ i, i < 12 → D.getLsbD i = false)
    (hhi : ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32) :
    ((adrpWordOff 0x90000008#32 D).extractLsb' 5 19 ++
      (adrpWordOff 0x90000008#32 D).extractLsb' 29 2).signExtend 64 <<< 12 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getMsbD]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm


theorem wC_mask : adrWordOff 0x10000008#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_31 : (adrWordOff 0x10000008#32 D).getLsbD 31 = false := by
  simp [adrWordOff]

theorem wC_rd : (adrWordOff 0x10000008#32 D).extractLsb' 0 5 = 8#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_off (hhi : ∀ i, 20 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 20) :
    ((adrWordOff 0x10000008#32 D).extractLsb' 5 19 ++
      (adrWordOff 0x10000008#32 D).extractLsb' 29 2).signExtend 64 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | rfl | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm

theorem wB_mask : lo12Word 0 0x91000108#32 D &&& 0x1f800000#32 = 0x11000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wB_bits : (lo12Word 0 0x91000108#32 D).getLsbD 31 = true ∧
    (lo12Word 0 0x91000108#32 D).getLsbD 30 = false ∧
    (lo12Word 0 0x91000108#32 D).getLsbD 29 = false ∧
    (lo12Word 0 0x91000108#32 D).getLsbD 22 = false := by
  simp [lo12Word]

theorem wB_rd : (lo12Word 0 0x91000108#32 D).extractLsb' 0 5 = 8#5 ∧
    (lo12Word 0 0x91000108#32 D).extractLsb' 5 5 = 8#5 := by
  constructor <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem wB_imm : (lo12Word 0 0x91000108#32 D).extractLsb' 10 12 = D.extractLsb' 0 12 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

end words

theorem decode_A {P T : BitVec 64} (hr : AdrpInRange P T) :
    decode (adrpWord 0x90000008#32 P T) = some (.adr true (.gpr 8#5) (pageOf T - pageOf P)) := by
  rw [adrpWord, decode_adr_class _ (wA_mask _), wA_31, wA_rd,
    wA_off _ (lo_bits T P) (hi_bits32 _ hr.1 hr.2)]
  rfl

theorem decode_C {P T : BitVec 64} (hr : AdrInRange P T) :
    decode (adrWord (adrTemplate 0x91000108#32) P T) = some (.adr false (.gpr 8#5) (T - P)) := by
  rw [adrWord, show adrTemplate 0x91000108#32 = 0x10000008#32 by decide,
    decode_adr_class _ (wC_mask _), wC_31, wC_rd, if_neg (by decide), wC_off _ (hi_bits20 _ hr.1 hr.2)]
  rfl

theorem decode_B (T : BitVec 64) :
    decode (lo12Word 0 0x91000108#32 T) =
      some (.addSubImm .W64 .ADD (.gpr 8#5) (.gpr 8#5) (T.extractLsb' 0 12) false) := by
  obtain ⟨b31, b30, b29, b22⟩ := wB_bits T
  rw [decode_addimm_class _ (wB_mask _), b31, b30, b29, b22, wB_rd T |>.1, wB_rd T |>.2, wB_imm]
  rfl

theorem decode_nop : decode nopWord = some .nop := by decide

theorem pc_add (b : BitVec 64) (n k : Nat) :
    b + BitVec.ofNat 64 n + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (n + k) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem target_T (pl : Placement) (o : Nat) (k : RelocKind) :
    zlibCrc32Text.target pl { off := o, kind := k, sym := tsym } = pl.ρ tsym := by
  have hlk : lookup tsym zlibCrc32Text.symbols = none := by decide
  simp [CodeBlock.target, CodeBlock.resolve, hlk, addSignedAddr]

theorem range_adrp {pl : Placement} (hP : zlibCrc32Lib.Placeable pl) (o : Nat) (ho : o = 28 ∨ o = 224) :
    AdrpInRange (pl.base + BitVec.ofNat 64 o) (pl.ρ tsym) := by
  have hmem : ({ off := o, kind := .adrpHi21, sym := tsym } : RelocEntry) ∈ zlibCrc32Text.relocs := by
    rcases ho with rfl | rfl <;> decide
  have h := (hP.text.relocs_ok _ hmem).2.2
  have ht : zlibCrc32Text.relocTarget pl o { off := o, kind := .adrpHi21, sym := tsym } = pl.ρ tsym := by
    simp only [CodeBlock.relocTarget, CodeBlock.b2bNext?]
    simp [target_T]
  simp only [zlibCrc32Lib] at h
  rw [ht] at h
  exact h

theorem range_adr {pl : Placement} (hP : zlibCrc32Lib.Placeable pl) (o : Nat) (ho : o = 28 ∨ o = 224)
    (hrel : pl.relax o = true) :
    AdrInRange (pl.base + BitVec.ofNat 64 (o + 4)) (pl.ρ tsym) := by
  have h1 : zlibCrc32Text.relaxableAt o = true := by rcases ho with rfl | rfl <;> decide
  have hr : zlibCrc32Text.relocAt? (o + 4) = some { off := o + 4, kind := .addLo12, sym := tsym } := by
    rcases ho with rfl | rfl <;> rfl
  have hPt : zlibCrc32Text.Placeable pl := hP.text
  have h := hPt.relaxed_ok o _ (by simp [CodeBlock.relaxedAt, h1, hrel]) hr
  rwa [target_T] at h

theorem awc_add (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]; omega

theorem steps_pair {pl : Placement} {s0 : State} {x0 x1 x2 x8 x9 x10 x11 : BitVec 64} {ps : PState}
    (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded s0.mem)
    (hrun : s0.status = .Running) (o : Nat) (ho : o = 28 ∨ o = 224) :
    Steps (prog pl) (mkS s0 (pl.base + BitVec.ofNat 64 o) x0 x1 x2 x8 x9 x10 x11 ps)
      (mkS s0 (pl.base + BitVec.ofNat 64 (o + 8)) x0 x1 x2 (pl.ρ tsym) x9 x10 x11 ps) := by
  have hal : o % 4 = 0 := by rcases ho with rfl | rfl <;> rfl
  have hle : o + 8 ≤ 1056 := by rcases ho with rfl | rfl <;> decide
  have hf2 := fetch_word hP hCL (off := o + 4) (by omega) (by omega)
  rw [pw_add pl o ho] at hf2
  have hf1 := fetch_word hP hCL (off := o) hal (by omega)
  rw [pw_adrp pl o ho] at hf1
  have p4 := pc_add pl.base o 4
  have p8 := pc_add pl.base (o + 4) 4
  rw [show o + 4 + 4 = o + 8 by omega] at p8
  cases h : pl.relax o
  · simp only [h, Bool.false_eq_true, if_false] at hf1 hf2
    rw [decode_A (range_adrp hP o ho)] at hf1
    rw [decode_B] at hf2
    refine Steps.step (s2 := mkS s0 (pl.base + BitVec.ofNat 64 (o + 4)) x0 x1 x2
      (pageOf (pl.ρ tsym)) x9 x10 x11 ps) (step_mkS hrun hf1 ?_) (Steps.one (step_mkS hrun hf2 ?_))
    · rw [ex_adr]; simp only [if_true, wr_x8, mkS_advancePC, mkS_pc]; rw [p4]
      congr 1
      have e : ∀ a b : BitVec 64, a + (b - a) = b := by intro a b; bv_omega
      rw [show (pl.base + BitVec.ofNat 64 o) &&& 0xfffffffffffff000#64 =
        pageOf (pl.base + BitVec.ofNat 64 o) from rfl, e]
    · rw [ex_addSubImm]
      simp only [execAddSubImm, State.readReg, rd_x8, evalAddSub, awc_add, State.writeReg, wr_x8,
        mkS_advancePC, Bool.false_eq_true, if_false]
      rw [p8]
      congr 1
      exact page_add_lo _
  · simp only [h, if_true] at hf1 hf2
    rw [decode_nop] at hf1
    rw [decode_C (range_adr hP o ho h)] at hf2
    refine Steps.step (s2 := mkS s0 (pl.base + BitVec.ofNat 64 (o + 4)) x0 x1 x2
      x8 x9 x10 x11 ps) (step_mkS hrun hf1 ?_) (Steps.one (step_mkS hrun hf2 ?_))
    · rw [ex_nop]; simp only [mkS_advancePC]; rw [p4]
    · rw [ex_adr]; simp only [Bool.false_eq_true, if_false, wr_x8, mkS_advancePC, mkS_pc]
      rw [p8]; congr 1; bv_omega

end ZlibCrc32Bytewise.Proof
end

section
/-! # Memory facts from the precondition -/

namespace ZlibCrc32Bytewise.Proof

open Arm64 Arm64.Obj

theorem ro_union_left {h1 h2 : Heap} {a : BitVec 64} {b : BitVec 8}
    (h : h1.phys a = some (.ro b)) : (h1.union h2).phys a = some (.ro b) := by
  simp [Heap.union, h]

theorem ro_union_right {h1 h2 : Heap} (hd : h1.Disjoint h2) {a : BitVec 64} {b : BitVec 8}
    (h : h2.phys a = some (.ro b)) : (h1.union h2).phys a = some (.ro b) := by
  rcases hd.1 a with h0 | h0 | ⟨b', e1, e2⟩
  · simp [Heap.union, h0, h]
  · rw [h] at h0; cases h0
  · rw [h] at e2; cases e2; simp [Heap.union, e1]

theorem sep_left {P Q : SepProp} {h : Heap} (hs : (P ∗ Q).holds h) {a : BitVec 64} {b : BitVec 8}
    (hP : ∀ h1, P.holds h1 → h1.phys a = some (.ro b)) : h.phys a = some (.ro b) := by
  obtain ⟨h1, h2, _, rfl, p1, _⟩ := hs
  exact ro_union_left (hP h1 p1)

theorem sep_right {P Q : SepProp} {h : Heap} (hs : (P ∗ Q).holds h) {a : BitVec 64} {b : BitVec 8}
    (hQ : ∀ h2, Q.holds h2 → h2.phys a = some (.ro b)) : h.phys a = some (.ro b) := by
  obtain ⟨h1, h2, hd, rfl, _, q2⟩ := hs
  exact ro_union_right hd (hQ h2 q2)

theorem ro_bytes : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap),
    (pointsToBytesRO a bs).holds h → ∀ i (hi : i < bs.length),
      h.phys (a + BitVec.ofNat 64 i) = some (.ro bs[i])
  | [], _, _, _, i, hi => by simp at hi
  | b :: bs, a, h, hs, i, hi => by
    simp only [pointsToBytesRO] at hs
    cases i with
    | zero =>
      refine sep_left hs fun h1 p1 => ?_
      simp only [pointsTo8RO] at p1
      subst p1; simp [Heap.singletonRO]
    | succ i =>
      refine sep_right hs fun h2 p2 => ?_
      have := ro_bytes bs (a + 1#64) h2 p2 i (by simp at hi; omega)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm] at this
      simpa using this

/-- What a matched read-only cell gives about memory. -/
theorem ro_matches {h : Heap} {m : Memory} (hm : h.Matches m) {a : BitVec 64} {b : BitVec 8}
    (hc : h.phys a = some (.ro b)) :
    m.read8 a = b ∧ (m.perm a).r = true ∧ m.isLazyFree a = false := by
  have := hm.1 a _ hc
  exact this

/-- Readable bytes `bs` at `a`. -/
def RoBytes (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) : Prop :=
  ∀ i (hi : i < bs.length), m.read8 (a + BitVec.ofNat 64 i) = bs[i] ∧
    (m.perm (a + BitVec.ofNat 64 i)).r = true ∧ m.isLazyFree (a + BitVec.ofNat 64 i) = false

theorem dataInit_eq (pl : Placement) :
    zlibCrc32Lib.dataInit pl =
      (pointsToBytesRO (pl.ρ "crc_table [zlib_crc32]") zlibCrc32PlacedData0 ∗
        pointsToBytesRO (pl.ρ "x2n_table [zlib_crc32]") zlibCrc32PlacedData1) := by
  simp only [PlacedLib.dataInit, zlibCrc32Lib, zlibCrc32Data, List.map, sepAll,
    PlacedLib.patchedData, List.foldl, List.replicate, List.append_nil, if_true]

/-- Everything the proof needs from the precondition. -/
theorem pre_facts {pl : Placement} {bs : List (BitVec 8)} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (crc32zSpec pl).pre bs s0 ∗ R) :
    s0.readReg64 (.gpr 1#5) ≠ 0#64 ∧ (s0.readReg64 (.gpr 2#5)).toNat = bs.length ∧
    RoBytes s0.mem (s0.readReg64 (.gpr 1#5)) bs ∧
    RoBytes s0.mem (pl.ρ "crc_table [zlib_crc32]") zlibCrc32PlacedData0 := by
  obtain ⟨h, hh, hm⟩ := hpre
  obtain ⟨h1, h2, _, rfl, hpre1, _⟩ := hh
  simp only [crc32zSpec] at hpre1
  obtain ⟨g1, g2, _, rfl, ⟨_, hφ⟩, hrest⟩ := hpre1
  refine ⟨hφ.1, hφ.2, ?_, ?_⟩
  · intro i hi
    refine ro_matches hm (ro_union_left (ro_union_right ‹_› (sep_left hrest fun k pk => ?_)))
    exact ro_bytes bs _ k pk i hi
  · intro i hi
    refine ro_matches hm (ro_union_left (ro_union_right ‹_› (sep_right hrest fun k pk => ?_)))
    rw [dataInit_eq] at pk
    exact sep_left pk fun k' pk' => ro_bytes _ _ k' pk' i hi

/-- The postcondition holds in the unchanged memory once its pure part does. -/
theorem post_of_pre {pl : Placement} {bs : List (BitVec 8)} {s0 sf : State} {R : SepProp}
    (hpre : s0.mem ⊨ (crc32zSpec pl).pre bs s0 ∗ R)
    (hx0 : sf.readReg64 Reg.x0 =
      (crcModel zlibCrc32PlacedData0 ((s0.readReg64 Reg.x0).truncate 32) bs).zeroExtend 64) :
    s0.mem ⊨ (crc32zSpec pl).post bs s0 sf ∗ R := by
  obtain ⟨h, hh, hm⟩ := hpre
  refine ⟨h, ?_, hm⟩
  obtain ⟨h1, h2, hd, rfl, hpre1, hr⟩ := hh
  refine ⟨h1, h2, hd, rfl, ?_, hr⟩
  simp only [crc32zSpec] at hpre1 ⊢
  obtain ⟨g1, g2, hd', rfl, ⟨he, _⟩, hrest⟩ := hpre1
  exact ⟨g1, g2, hd', rfl, ⟨he, hx0⟩, hrest⟩

end ZlibCrc32Bytewise.Proof
end

section
/-! # Value lemmas: one table step, flags -/

namespace ZlibCrc32Bytewise.Proof

open Arm64 Arm64.Obj

abbrev tbl : List (BitVec 8) := zlibCrc32PlacedData0

set_option maxRecDepth 100000 in
theorem tbl_length : tbl.length = 1024 := by rfl

theorem canRead1 {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} (h : RoBytes m a bs)
    (i : Nat) (hi : i < bs.length) : m.canRead (a + BitVec.ofNat 64 i) 1 = true := by
  obtain ⟨_, h2, h3⟩ := h i hi
  simp [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree, h2, h3]

theorem xor_trunc (b : BitVec 8) (c : BitVec 32) :
    ((b.zeroExtend 64 : BitVec 64).truncate 32 ^^^ (c.zeroExtend 64 : BitVec 64).truncate 32) =
      c ^^^ b.zeroExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp [Bool.xor_comm]

theorem idx_eq (b : BitVec 8) (c : BitVec 32) :
    ((((b.zeroExtend 64 : BitVec 64).truncate 32 ^^^ (c.zeroExtend 64 : BitVec 64).truncate 32)
      ).zeroExtend 64 &&& 0xff#64) <<< 2 =
      BitVec.ofNat 64 (4 * ((c ^^^ b.zeroExtend 32).toNat % 256)) := by
  rw [xor_trunc]
  apply BitVec.eq_of_toNat_eq
  have h255 : ∀ x : Nat, x &&& 255 = x % 256 := fun x => Nat.and_two_pow_sub_one_eq_mod x 8
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  have := (c ^^^ b.zeroExtend 32).isLt
  generalize (c ^^^ b.zeroExtend 32).toNat = x at *
  rw [show (255 : Nat) % 2 ^ 64 = 255 from rfl, Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), h255]
  omega

theorem zx_xor_shr (t c : BitVec 32) :
    (t.zeroExtend 64 : BitVec 64) ^^^ ((c.zeroExtend 64 : BitVec 64) >>> 8) =
      ((c >>> 8) ^^^ t).zeroExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp [Bool.xor_comm]

theorem read32_tbl {m : Memory} {T : BitVec 64} (ht : RoBytes m T tbl) (j : Nat) (hj : j < 256) :
    m.canRead (T + BitVec.ofNat 64 (4 * j)) 4 = true ∧
    m.read32 (T + BitVec.ofNat 64 (4 * j)) = tableEntry tbl j := by
  have e : ∀ k, k < 4 → T + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 k =
      T + BitVec.ofNat 64 (4 * j + k) := fun k _ => pc_add _ _ _
  have r0 := ht (4 * j) (by rw [tbl_length]; omega)
  have r1 := ht (4 * j + 1) (by rw [tbl_length]; omega)
  have r2 := ht (4 * j + 2) (by rw [tbl_length]; omega)
  have r3 := ht (4 * j + 3) (by rw [tbl_length]; omega)
  rw [← e 1 (by omega)] at r1
  rw [← e 2 (by omega)] at r2
  rw [← e 3 (by omega)] at r3
  constructor
  · simp only [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree, BitVec.add_assoc,
      BitVec.reduceAdd] at *
    simp [r0.2.1, r0.2.2, r1.2.1, r1.2.2, r2.2.1, r2.2.2, r3.2.1, r3.2.2]
  · simp only [Memory.read32, tableEntry]
    have : T + BitVec.ofNat 64 (4 * j) + 0#64 = T + BitVec.ofNat 64 (4 * j) := by simp
    rw [this, r0.1, r1.1, r2.1, r3.1]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem, List.getElem?_eq_getElem, List.getElem?_eq_getElem,
      List.getElem?_eq_getElem]
    · rfl

/-- One byte of the loop: the table lookup and the new `x9`. -/
theorem tab_step {m : Memory} {T : BitVec 64} (ht : RoBytes m T tbl) (c : BitVec 32) (b : BitVec 8) :
    m.canRead (T + (((((b.zeroExtend 64 : BitVec 64).truncate 32 ^^^
        (c.zeroExtend 64 : BitVec 64).truncate 32)).zeroExtend 64 &&& 0xff#64) <<< 2)) 4 = true ∧
    ((m.read32 (T + (((((b.zeroExtend 64 : BitVec 64).truncate 32 ^^^
        (c.zeroExtend 64 : BitVec 64).truncate 32)).zeroExtend 64 &&& 0xff#64) <<< 2))).zeroExtend 64
      ^^^ ((c.zeroExtend 64 : BitVec 64) >>> 8)) = (crcStep tbl c b).zeroExtend 64 := by
  rw [idx_eq]
  have hj : (c ^^^ b.zeroExtend 32).toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  obtain ⟨h1, h2⟩ := read32_tbl ht _ hj
  refine ⟨h1, ?_⟩
  rw [h2, zx_xor_shr]; rfl

end ZlibCrc32Bytewise.Proof
end

section
/-! # Reachability of the return state: groups, loops -/

namespace ZlibCrc32Bytewise.Proof

open Arm64 Arm64.Obj

/-- Returned with `x0 = X`, everything else in the abstract frame. -/
def Fin (s0 : State) (X : BitVec 64) (sf : State) : Prop :=
  ∃ x1 x2 x8 x9 x10 x11 : BitVec 64, ∃ ps : PState,
    sf = mkS s0 (s0.readReg64 (.gpr 30#5)) X x1 x2 x8 x9 x10 x11 ps

def Reach (pl : Placement) (s0 : State) (X : BitVec 64) (s : State) : Prop :=
  ∃ sf, Steps (prog pl) s sf ∧ Fin s0 X sf

theorem reach_step {pl : Placement} {s0 s s' : State} {X : BitVec 64} (h : Step (prog pl) s s')
    (h' : Reach pl s0 X s') : Reach pl s0 X s := by
  obtain ⟨sf, h1, h2⟩ := h'
  exact ⟨sf, Steps.step h h1, h2⟩

theorem reach_steps {pl : Placement} {s0 s s' : State} {X : BitVec 64} (h : Steps (prog pl) s s')
    (h' : Reach pl s0 X s') : Reach pl s0 X s := by
  obtain ⟨sf, h1, h2⟩ := h'
  exact ⟨sf, Steps.trans' h h1, h2⟩

theorem subFlags_c (x y : BitVec 64) : (subFlags x y).c = decide (y.toNat ≤ x.toNat) := by
  simp only [subFlags, AddWithCarry64, BitVec.msb_eq_decide]
  simp [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_not]
  omega

theorem subFlags_z (x y : BitVec 64) : (subFlags x y).z = decide (x.toNat = y.toNat) := by
  simp only [subFlags, AddWithCarry64, if_true]
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← BitVec.toNat_inj]
  simp [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_not]
  omega

section
variable {pl : Placement} {s0 : State} {X : BitVec 64}

/-- A plain byte group `ldrb w10,[x1,#k]; eor; and; ldr w10; eor x9` at block offset `N`. -/
theorem grp (hrun : s0.status = .Running) {N : Nat} {k : BitVec 64}
    {x0 x1 x2 x8 x10 x11 : BitVec 64} {ps : PState} {c : BitVec 32}
    (f0 : (prog pl).fetchMem s0.mem (pl.base + BitVec.ofNat 64 N) = some (iLdrb k))
    (f1 : (prog pl).fetchMem s0.mem (pl.base + BitVec.ofNat 64 (N + 4)) = some iEorW)
    (f2 : (prog pl).fetchMem s0.mem (pl.base + BitVec.ofNat 64 (N + 4 + 4)) = some iAnd)
    (f3 : (prog pl).fetchMem s0.mem (pl.base + BitVec.ofNat 64 (N + 4 + 4 + 4)) = some (iLdrT 10#5))
    (f4 : (prog pl).fetchMem s0.mem (pl.base + BitVec.ofNat 64 (N + 4 + 4 + 4 + 4)) =
      some (iEorX 10#5))
    (hr : s0.mem.canRead (x1 + k) 1 = true) (ht : RoBytes s0.mem x8 tbl)
    (h : ∀ x10' : BitVec 64, Reach pl s0 X (mkS s0 (pl.base + BitVec.ofNat 64 (N + 4 + 4 + 4 + 4 + 4))
      x0 x1 x2 x8 ((crcStep tbl c (s0.mem.read8 (x1 + k))).zeroExtend 64) x10' x11 ps)) :
    Reach pl s0 X (mkS s0 (pl.base + BitVec.ofNat 64 N) x0 x1 x2 x8 (c.zeroExtend 64) x10 x11 ps) := by
  have hts := tab_step ht c (s0.mem.read8 (x1 + k))
  refine reach_step (s_ldrb hrun f0 hr) ?_
  rw [pc_add]; refine reach_step (s_eorW hrun f1) ?_
  rw [pc_add]; refine reach_step (s_and hrun f2) ?_
  rw [pc_add]; refine reach_step (s_ldrT10 hrun f3 hts.1) ?_
  rw [pc_add]; refine reach_step (s_eorX10 hrun f4) ?_
  rw [pc_add, hts.2]
  exact h _

end

/-- The CRC state after the first `q` bytes. -/
def runT (bs : List (BitVec 8)) (c0 : BitVec 32) (q : Nat) : BitVec 32 :=
  (bs.take q).foldl (crcStep tbl) c0

theorem runT_succ (bs : List (BitVec 8)) (c0 : BitVec 32) (q : Nat) (hq : q < bs.length) :
    crcStep tbl (runT bs c0 q) bs[q] = runT bs c0 (q + 1) := by
  rw [runT, runT, List.take_succ_eq_append_getElem hq, List.foldl_append]; rfl

theorem runT_all (bs : List (BitVec 8)) (c0 : BitVec 32) :
    runT bs c0 bs.length = bs.foldl (crcStep tbl) c0 := by
  simp [runT]

theorem fin_val (v : BitVec 32) :
    (v.zeroExtend 64 : BitVec 64) ^^^ 0xffffffff#64 = (~~~v).zeroExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, BitVec.getLsbD_not]
  interval_cases i <;> simp

theorem ofNat_sub_ofNat (r k : Nat) (hk : k ≤ r) (hr : r < 2 ^ 64) :
    BitVec.ofNat 64 r - BitVec.ofNat 64 k = BitVec.ofNat 64 (r - k) := by
  have hr' : r < 18446744073709551616 := hr
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub, Nat.mod_eq_of_lt hr']
  omega

theorem toNat_ofNat_lt (r : Nat) (hr : r < 2 ^ 64) : (BitVec.ofNat 64 r).toNat = r := by
  have hr' : r < 18446744073709551616 := hr
  simp [Nat.mod_eq_of_lt hr']

section main
variable {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {c0 : BitVec 32}
  (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded s0.mem)
  (hrun : s0.status = .Running)
  (hbuf : RoBytes s0.mem (s0.readReg64 (.gpr 1#5)) bs) (htab : RoBytes s0.mem (pl.ρ tsym) tbl)
  (hn : bs.length < 2 ^ 64)


include hP hCL hrun in
theorem fin260 (x0 x1 x2 x8 x10 x11 : BitVec 64) (ps : PState) :
    Reach pl s0 ((~~~ (bs.foldl (crcStep tbl) c0)).zeroExtend 64) (mkS s0 (pl.base + 260#64) x0 x1 x2 x8
      ((bs.foldl (crcStep tbl) c0).zeroExtend 64) x10 x11 ps) := by
  refine reach_step (s_eorFin hrun (f_f8 hP hCL)) ?_
  rw [pc_add, fin_val]
  refine reach_step (s_ret hrun (f_fc hP hCL)) ?_
  exact ⟨_, Steps.refl _, _, _, _, _, _, _, _, rfl⟩

theorem adv {s0 : State} {bs : List (BitVec 8)} {c0 : BitVec 32} {p k q : Nat} (hq : p + k = q) (hqn : q < bs.length) (hbuf : RoBytes s0.mem (s0.readReg64 (.gpr 1#5)) bs) :
    crcStep tbl (runT bs c0 q) (s0.mem.read8 ((s0.readReg64 (.gpr 1#5)) + BitVec.ofNat 64 p + BitVec.ofNat 64 k)) =
      runT bs c0 (q + 1) := by
  rw [pc_add, hq, (hbuf q hqn).1, runT_succ _ _ _ hqn]

include hP hCL hrun hbuf htab hn in
theorem tail232 (r : Nat) : ∀ (p : Nat) (x0 x10 x11 : BitVec 64) (ps : PState), 1 ≤ r →
    p + r = bs.length →
    Reach pl s0 ((~~~ (bs.foldl (crcStep tbl) c0)).zeroExtend 64) (mkS s0 (pl.base + 232#64) x0 ((s0.readReg64 (.gpr 1#5)) + BitVec.ofNat 64 p) (BitVec.ofNat 64 r)
      (pl.ρ tsym) ((runT bs c0 p).zeroExtend 64) x10 x11 ps) := by
  induction r with
  | zero => intro p x0 x10 x11 ps h; omega
  | succ r ih =>
    intro p x0 x10 x11 ps _ hpr
    have hp : p < bs.length := by omega
    have hts := tab_step htab (runT bs c0 p) (s0.mem.read8 ((s0.readReg64 (.gpr 1#5)) + BitVec.ofNat 64 p))
    refine reach_step (s_ldrbPost hrun (f_dc hP hCL) (canRead1 hbuf p hp)) ?_
    simp only [pc_add]
    refine reach_step (s_subs1 hrun (f_e0 hP hCL)) ?_
    simp only [pc_add]
    refine reach_step (s_eorW hrun (f_e4 hP hCL)) ?_
    simp only [pc_add]
    refine reach_step (s_and hrun (f_e8 hP hCL)) ?_
    simp only [pc_add]
    refine reach_step (s_ldrT10 hrun (f_ec hP hCL) hts.1) ?_
    simp only [pc_add]
    refine reach_step (s_eorX10 hrun (f_f0 hP hCL)) ?_
    simp only [pc_add]
    rw [hts.2, (hbuf p hp).1, runT_succ _ _ _ hp]
    have hz := subFlags_z (BitVec.ofNat 64 (r + 1)) 1#64
    rw [toNat_ofNat_lt _ (by omega)] at hz
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · -- last byte: fall through to 0xf8
      subst hr0
      refine reach_step (s_bCond_f hrun (f_f4 hP hCL) (by simp [ConditionHolds, hz])) ?_
      simp only [pc_add]
      have : p + 1 = bs.length := by omega
      rw [this, runT_all]
      exact fin260 hP hCL hrun _ _ _ _ _ _ _
    · refine reach_step (s_bCond_t hrun (f_f4 hP hCL) (by simp [ConditionHolds, hz]; omega)) ?_
      rw [show pl.base + BitVec.ofNat 64 (232 + 4 + 4 + 4 + 4 + 4 + 4) + 0xffffffffffffffe8#64 =
        pl.base + 232#64 by rw [BitVec.add_assoc]; rfl]
      rw [ofNat_sub_ofNat _ _ (by omega) (by omega), show r + 1 - 1 = r by omega]
      exact ih (p + 1) _ _ _ _ hr0 (by omega)

include hP hCL hrun hbuf htab hn in
theorem entry220 (p r : Nat) (x0 x8 x10 x11 : BitVec 64) (ps : PState) (hpr : p + r = bs.length) :
    Reach pl s0 ((~~~ (bs.foldl (crcStep tbl) c0)).zeroExtend 64) (mkS s0 (pl.base + 220#64) x0 ((s0.readReg64 (.gpr 1#5)) + BitVec.ofNat 64 p)
      (BitVec.ofNat 64 r) x8 ((runT bs c0 p).zeroExtend 64) x10 x11 ps) := by
  cases r with
  | zero =>
    refine reach_step (s_cbzX2_t hrun (f_d0 hP hCL)) ?_
    rw [show pl.base + 220#64 + 0x28#64 = pl.base + 260#64 by rw [BitVec.add_assoc]; rfl]
    rw [show p = bs.length by omega, runT_all]
    exact fin260 hP hCL hrun _ _ _ _ _ _ _
  | succ r =>
    have hne : BitVec.ofNat 64 (r + 1) ≠ 0#64 := by
      intro h; have := congrArg BitVec.toNat h
      rw [toNat_ofNat_lt _ (by omega)] at this; simp at this
    refine reach_step (s_cbzX2_f hrun (f_d0 hP hCL) hne) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    refine reach_steps (steps_pair hP hCL hrun 224 (Or.inr rfl)) ?_
    exact tail232 hP hCL hrun hbuf htab hn (r + 1) p _ _ _ _ (by omega) hpr

include hP hCL hrun hbuf htab hn in
theorem head36 (r : Nat) : ∀ (p : Nat) (x0 x10 x11 : BitVec 64) (ps : PState), 8 ≤ r →
    p + r = bs.length →
    Reach pl s0 ((~~~ (bs.foldl (crcStep tbl) c0)).zeroExtend 64) (mkS s0 (pl.base + 36#64) x0 ((s0.readReg64 (.gpr 1#5)) + BitVec.ofNat 64 p) (BitVec.ofNat 64 r)
      (pl.ρ tsym) ((runT bs c0 p).zeroExtend 64) x10 x11 ps) := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro p x0 x10 x11 ps h8 hpr
    have hb : ∀ k : Nat, k < 8 → s0.mem.canRead ((s0.readReg64 (.gpr 1#5)) + BitVec.ofNat 64 p + BitVec.ofNat 64 k) 1 = true :=
      fun k hk => by rw [pc_add]; exact canRead1 hbuf _ (by omega)
    have hts0 := tab_step htab (runT bs c0 p) (s0.mem.read8 ((s0.readReg64 (.gpr 1#5)) + BitVec.ofNat 64 p + 0#64))
    refine reach_step (s_ldrb hrun (f_18 hP hCL) (hb 0 (by omega))) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    refine reach_step (s_sub8 hrun (f_1c hP hCL)) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    refine reach_step (s_cmp7 hrun (f_20 hP hCL)) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    refine reach_step (s_eorW hrun (f_24 hP hCL)) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    refine reach_step (s_and hrun (f_28 hP hCL)) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    refine reach_step (s_ldrT10 hrun (f_2c hP hCL) hts0.1) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    refine reach_step (s_eorX10 hrun (f_30 hP hCL)) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    rw [hts0.2, adv (p := p) (k := 0) (q := p) (by omega) (by omega) hbuf]
    refine grp hrun (f_34 hP hCL) (f_38 hP hCL) (f_3c hP hCL) (f_40 hP hCL)
      (f_44 hP hCL) (hb 1 (by omega)) htab (fun x10' => ?_)
    simp only [pc_add pl.base, Nat.reduceAdd]
    rw [adv (p := p) (k := 1) (q := p + 1) (by omega) (by omega) hbuf]
    refine grp hrun (f_48 hP hCL) (f_4c hP hCL) (f_50 hP hCL) (f_54 hP hCL)
      (f_58 hP hCL) (hb 2 (by omega)) htab (fun x10' => ?_)
    simp only [pc_add pl.base, Nat.reduceAdd]
    rw [adv (p := p) (k := 2) (q := p + 1 + 1) (by omega) (by omega) hbuf]
    refine grp hrun (f_5c hP hCL) (f_60 hP hCL) (f_64 hP hCL) (f_68 hP hCL)
      (f_6c hP hCL) (hb 3 (by omega)) htab (fun x10' => ?_)
    simp only [pc_add pl.base, Nat.reduceAdd]
    rw [adv (p := p) (k := 3) (q := p + 1 + 1 + 1) (by omega) (by omega) hbuf]
    refine grp hrun (f_70 hP hCL) (f_74 hP hCL) (f_78 hP hCL) (f_7c hP hCL)
      (f_80 hP hCL) (hb 4 (by omega)) htab (fun x10' => ?_)
    simp only [pc_add pl.base, Nat.reduceAdd]
    rw [adv (p := p) (k := 4) (q := p + 1 + 1 + 1 + 1) (by omega) (by omega) hbuf]
    refine grp hrun (f_84 hP hCL) (f_88 hP hCL) (f_8c hP hCL) (f_90 hP hCL)
      (f_94 hP hCL) (hb 5 (by omega)) htab (fun x10' => ?_)
    simp only [pc_add pl.base, Nat.reduceAdd]
    rw [adv (p := p) (k := 5) (q := p + 1 + 1 + 1 + 1 + 1) (by omega) (by omega) hbuf]
    refine grp hrun (f_98 hP hCL) (f_9c hP hCL) (f_a0 hP hCL) (f_a4 hP hCL)
      (f_a8 hP hCL) (hb 6 (by omega)) htab (fun x10' => ?_)
    simp only [pc_add pl.base, Nat.reduceAdd]
    rw [adv (p := p) (k := 6) (q := p + 1 + 1 + 1 + 1 + 1 + 1) (by omega) (by omega) hbuf]
    have hts7 := tab_step htab (runT bs c0 (p + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (s0.mem.read8 ((s0.readReg64 (.gpr 1#5)) + BitVec.ofNat 64 p + 7#64))
    refine reach_step (s_ldrb hrun (f_ac hP hCL) (hb 7 (by omega))) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    refine reach_step (s_eorW hrun (f_b0 hP hCL)) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    refine reach_step (s_and hrun (f_b4 hP hCL)) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    refine reach_step (s_ldrT11 hrun (f_b8 hP hCL) hts7.1) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    refine reach_step (s_add8 hrun (f_bc hP hCL)) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    refine reach_step (s_movX1 hrun (f_c0 hP hCL)) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    refine reach_step (s_eorX11 hrun (f_c4 hP hCL)) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    rw [hts7.2, adv (p := p) (k := 7) (q := p + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by omega) (by omega) hbuf]
    rw [pc_add (s0.readReg64 (.gpr 1#5)), show p + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = p + 8 by omega, ofNat_sub_ofNat _ _ (by omega) (by omega)]
    have hc := subFlags_c (BitVec.ofNat 64 (r - 8)) 7#64
    have hz := subFlags_z (BitVec.ofNat 64 (r - 8)) 7#64
    rw [toNat_ofNat_lt _ (by omega)] at hc hz
    by_cases hgo : 8 ≤ r - 8
    · refine reach_step (s_bCond_t hrun (f_c8 hP hCL) (by simp [ConditionHolds, hc, hz]; omega)) ?_
      rw [show pl.base + 212#64 + 0xffffffffffffff50#64 = pl.base + 36#64 by
        rw [BitVec.add_assoc]; rfl]
      exact ih (r - 8) (by omega) (p + 8) _ _ _ _ hgo (by omega)
    · refine reach_step (s_bCond_f hrun (f_c8 hP hCL) (by simp [ConditionHolds, hc, hz]; omega)) ?_
      simp only [pc_add pl.base, Nat.reduceAdd]
      refine reach_step (s_movX1 hrun (f_cc hP hCL)) ?_
      simp only [pc_add pl.base, Nat.reduceAdd]
      exact entry220 hP hCL hrun hbuf htab hn (p + 8) (r - 8) _ _ _ _ _ (by omega)

end main

end ZlibCrc32Bytewise.Proof
end

section
/-! # `crc32_z` meets its contract: `ZlibCrc32Bytewise.Proof.goal` -/

namespace ZlibCrc32Bytewise.Proof

open Arm64 Arm64.Obj

theorem mkS_self (s0 : State) :
    mkS s0 s0.pc (s0.readReg64 (.gpr 0#5)) (s0.readReg64 (.gpr 1#5)) (s0.readReg64 (.gpr 2#5))
      (s0.readReg64 (.gpr 8#5)) (s0.readReg64 (.gpr 9#5)) (s0.readReg64 (.gpr 10#5))
      (s0.readReg64 (.gpr 11#5)) s0.pstate = s0 := by
  have hr : mkRegs s0.regs (s0.readReg64 (.gpr 0#5)) (s0.readReg64 (.gpr 1#5))
      (s0.readReg64 (.gpr 2#5)) (s0.readReg64 (.gpr 8#5)) (s0.readReg64 (.gpr 9#5))
      (s0.readReg64 (.gpr 10#5)) (s0.readReg64 (.gpr 11#5)) = s0.regs := by
    cases hs : s0.regs with
    | mk f =>
      simp only [mkRegs, State.readReg64, RegFile.read, hs]
      congr 1; funext i
      split_ifs <;> simp_all
  simp only [mkS, hr]

section
variable {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {c0 : BitVec 32}

theorem start (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded s0.mem)
    (hrun : s0.status = .Running)
    (hbuf : RoBytes s0.mem (s0.readReg64 (.gpr 1#5)) bs) (htab : RoBytes s0.mem (pl.ρ tsym) tbl)
    (hn : bs.length < 2 ^ 64) {x0 x8 x9 x10 x11 : BitVec 64} {ps : PState}
    (hc0 : c0 = ~~~ (x0.truncate 32)) (hx1 : s0.readReg64 (.gpr 1#5) ≠ 0#64) :
    Reach pl s0 ((~~~ (bs.foldl (crcStep tbl) c0)).zeroExtend 64)
      (mkS s0 (pl.base + 12#64) x0 (s0.readReg64 (.gpr 1#5)) (BitVec.ofNat 64 bs.length)
        x8 x9 x10 x11 ps) := by
  refine reach_step (s_cbzX1 hrun (f_00 hP hCL) hx1) ?_
  simp only [pc_add pl.base, Nat.reduceAdd]
  refine reach_step (s_cmp8 hrun (f_04 hP hCL)) ?_
  simp only [pc_add pl.base, Nat.reduceAdd]
  refine reach_step (s_mvn hrun (f_08 hP hCL)) ?_
  simp only [pc_add pl.base, Nat.reduceAdd]
  have hc := subFlags_c (BitVec.ofNat 64 bs.length) 8#64
  rw [toNat_ofNat_lt _ hn] at hc
  rw [show (~~~ (x0.truncate 32)).zeroExtend 64 = ((runT bs c0 0).zeroExtend 64 : BitVec 64) by
    simp [runT, hc0]]
  rw [show s0.readReg64 (.gpr 1#5) = s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 0 by simp]
  by_cases h8 : bs.length < 8
  · refine reach_step (s_bCond_t hrun (f_0c hP hCL) (by simp [ConditionHolds, hc]; omega)) ?_
    rw [show pl.base + 24#64 + 0xc4#64 = pl.base + 220#64 by rw [BitVec.add_assoc]; rfl]
    exact entry220 hP hCL hrun hbuf htab hn 0 bs.length _ _ _ _ _ (by omega)
  · refine reach_step (s_bCond_f hrun (f_0c hP hCL) (by simp [ConditionHolds, hc]; omega)) ?_
    simp only [pc_add pl.base, Nat.reduceAdd]
    refine reach_steps (steps_pair hP hCL hrun 28 (Or.inl rfl)) ?_
    exact head36 hP hCL hrun hbuf htab hn bs.length 0 _ _ _ _ (by omega) (by omega)

end

theorem fnAddr_crc (pl : Placement) : zlibCrc32Lib.fnAddr pl "crc32_z" = pl.base + 12#64 := rfl

theorem goal : zlibCrc32Lib.subroutineOk "crc32_z" crc32zSpec := by
  refine ⟨by decide, ?_⟩
  intro pl hP bs R s0 hpc hrun hpre _ hCL
  change (prog pl).CodeLoaded s0.mem at hCL
  obtain ⟨hx1, hx2, hbuf, htab⟩ := pre_facts hpre
  have hn : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 (.gpr 2#5)).isLt
  have hx2' : s0.readReg64 (.gpr 2#5) = BitVec.ofNat 64 bs.length := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_ofNat_lt _ hn, hx2]
  have h := start (c0 := ~~~ ((s0.readReg64 (.gpr 0#5)).truncate 32)) hP hCL hrun hbuf htab hn
    (x8 := s0.readReg64 (.gpr 8#5)) (x9 := s0.readReg64 (.gpr 9#5))
    (x10 := s0.readReg64 (.gpr 10#5)) (x11 := s0.readReg64 (.gpr 11#5)) (ps := s0.pstate) rfl hx1
  rw [← hx2', ← fnAddr_crc, ← hpc, mkS_self] at h
  obtain ⟨sf, hsteps, x1, x2, x8, x9, x10, x11, ps, rfl⟩ := h
  refine ⟨_, hsteps, Or.inl ⟨⟨rfl, rfl, hrun⟩, ⟨rfl, ?_⟩, ?_⟩⟩
  · simp [CalleeSavedPreserved, State.readReg64, mkS, mkRegs, RegFile.read]
  · exact post_of_pre hpre rfl

end ZlibCrc32Bytewise.Proof
end

open ZlibCrc32Bytewise in
theorem solution : zlibCrc32Lib.subroutineOk "crc32_z" crc32zSpec := ZlibCrc32Bytewise.Proof.goal
