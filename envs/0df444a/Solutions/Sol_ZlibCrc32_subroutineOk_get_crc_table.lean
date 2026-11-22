-- Prove2me | solution 1 for ZlibCrc32.subroutineOk_get_crc_table
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T10:38:08.93797+00:00
-- url     : https://prove2.me/submissions/95cc7334-6151-4440-9126-71d3de534a86

import Mathlib.Tactic.IntervalCases
import Definitions.Def_ZlibCrc32_Spec
import Theorems.Thm_ZlibCrc32_crc_tables_eq

section
/-! # Instruction fetch, abstract states and single-step lemmas for `zlibCrc32Lib`

Adapted from the byte-table pilot proof (`ZlibCrc32Bytewise`): the abstract state replaces the
whole general-purpose register file by a function `r`, so that one step lemma covers an
instruction shape at every register. -/

namespace ZlibCrc32.Small

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-- The placed program the statements talk about. -/
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
theorem code_length : zlibCrc32PlacedCode.length = 2824 := by rfl

theorem patched_length (pl : Placement) : (zlibCrc32Text.patched pl).length = 2824 := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE]
  show (List.map (fun _ => 4) (List.range (zlibCrc32PlacedCode.length / 4))).sum = 2824
  rw [code_length]; rfl

theorem hook_none (pl : Placement) (pc : BitVec 64) : (prog pl).externAt? pc = none := by
  simp [prog, Program.externAt?, Program.hookAtOff?, PlacedLib.program, zlibCrc32Lib, zlibCrc32Text]

theorem read8_code {pl : Placement} {m : Memory} (hCL : (prog pl).CodeLoaded m) {off k : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 2824) (hk : k < 4) :
    m.read8 (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      (zlibCrc32Text.patchedWord pl off).extractLsb' (8 * k) 8 ∧
    m.perm (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
  have hl : (prog pl).code.length = 2824 := patched_length pl
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
    (hCL : (prog pl).CodeLoaded m) {off : Nat} (hal : off % 4 = 0) (hlen : off + 4 ≤ 2824) :
    (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      decode (zlibCrc32Text.patchedWord pl off) := by
  have hb4 : pl.base.toNat % 4 = 0 := by
    have := hP.text.base_aligned; simpa [zlibCrc32Lib, zlibCrc32Text] using this
  have hnw : pl.base.toNat + 2824 ≤ 2 ^ 64 := by
    have := hP.text.no_wrap
    have hl : zlibCrc32Text.code.length = 2824 := code_length
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

theorem patchedWord_plain (pl : Placement) {off : Nat} (h : zlibCrc32Text.relocAt? off = none) :
    zlibCrc32Text.patchedWord pl off = zlibCrc32Text.wordAt off := by
  simp [CodeBlock.patchedWord, h]

/-- Fetch at an unrelocated word: the decoded word of the object. -/
theorem fetch_plain {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded m) {off : Nat} {i : Instr} (hal : off % 4 = 0)
    (hlen : off + 4 ≤ 2824) (hr : zlibCrc32Text.relocAt? off = none)
    (hd : decode (zlibCrc32Text.wordAt off) = some i) :
    (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 off) = some i := by
  rw [fetch_word hP hCL hal hlen, patchedWord_plain pl hr, hd]

/-! ## Abstract states -/

/-- The entry state `s0` with the register file `r`, `pc` and flags replaced. -/
def mkS (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (ps : PState) : State :=
  { s0 with regs := ⟨r⟩, pc := pc, pstate := ps }

section lemmas
variable (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (ps : PState)

@[simp] theorem mkS_mem : (mkS s0 pc r ps).mem = s0.mem := rfl
@[simp] theorem mkS_pc : (mkS s0 pc r ps).pc = pc := rfl
@[simp] theorem mkS_sp : (mkS s0 pc r ps).sp = s0.sp := rfl
@[simp] theorem mkS_status : (mkS s0 pc r ps).status = s0.status := rfl
@[simp] theorem mkS_pstate : (mkS s0 pc r ps).pstate = ps := rfl
@[simp] theorem mkS_vregs : (mkS s0 pc r ps).vregs = s0.vregs := rfl

theorem rd_gpr (i : BitVec 5) :
    (mkS s0 pc r ps).readReg64 (.gpr i) = if i = 31#5 then 0#64 else r i := by
  simp [State.readReg64, RegFile.read, mkS]

@[simp] theorem rd_xzr : (mkS s0 pc r ps).readReg64 .xzr = 0#64 := rfl

theorem wr_gpr (i : BitVec 5) (v : BitVec 64) (hi : i ≠ 31#5) :
    (mkS s0 pc r ps).writeReg64 (.gpr i) v = mkS s0 pc (Function.update r i v) ps := by
  simp only [mkS, State.writeReg64, RegFile.write, beq_iff_eq, hi, if_false]
  congr 2; funext k; simp [Function.update_apply]

@[simp] theorem wr_xzr (v : BitVec 64) : (mkS s0 pc r ps).writeReg64 .xzr v = mkS s0 pc r ps := rfl
@[simp] theorem mkS_advancePC : (mkS s0 pc r ps).advancePC = mkS s0 (pc + 4#64) r ps := rfl
@[simp] theorem mkS_setPC (q : BitVec 64) : (mkS s0 pc r ps).setPC q = mkS s0 q r ps := rfl
@[simp] theorem mkS_setPState (q : PState) : (mkS s0 pc r ps).setPState q = mkS s0 pc r q := rfl

end lemmas

/-! ## Steps utilities -/

theorem Steps.trans' {p : Program} {a b c : State} (h1 : Steps p a b) (h2 : Steps p b c) :
    Steps p a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact Steps.step h (ih h2)

theorem step_mkS {pl : Placement} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {ps : PState} {inst : Instr} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem s0.mem pc = some inst) :
    Step (prog pl) (mkS s0 pc r ps) (execInstWithSvc (evalSvc Syscall.standard) inst (mkS s0 pc r ps)) := by
  have := Step.exec (prog := prog pl) (s := mkS s0 pc r ps) hrun hf
  rw [Program.evalInst] at this
  rwa [show (prog pl).svc = Syscall.standard from rfl] at this

/-! ## The 32-bit view of a register -/

/-- The low 32 bits. -/
abbrev lo (x : BitVec 64) : BitVec 32 := x.setWidth 32
/-- Zero extension of a 32-bit value. -/
abbrev W (v : BitVec 32) : BitVec 64 := v.setWidth 64

@[simp] theorem lo_W (v : BitVec 32) : lo (W v) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

/-! ## Execution of each instruction shape on an abstract state -/

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {ps : PState}

theorem ex_ret :
    execInstWithSvc svc (.ret (.gpr 30#5)) (mkS s0 pc r ps) = mkS s0 (r 30#5) r ps := by
  show State.setPC _ _ = _
  simp [rd_gpr]

end exec

end ZlibCrc32.Small
end

section
/-! # Decoding relocated `ADRP`/`ADD`/`ADR` words: the register-independent part

From the byte-table pilot proof. -/

namespace ZlibCrc32.Small

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

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


theorem decode_nop : decode nopWord = some .nop := by decide


theorem awc_add' (x y : BitVec 64) :
    BitVec.truncate 64 (0#65 + (BitVec.zeroExtend 65 y + BitVec.zeroExtend 65 x)) = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_setWidth]
  omega

end ZlibCrc32.Small
end

section
/-! # Relocated `ADRP x0, crc_table` + `ADD x0, x0, :lo12:` pair(s) at offsets 0 (generated) -/

namespace ZlibCrc32.Small

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

abbrev symTab : String := "crc_table [zlib_crc32]"

theorem pw_adrpTab (pl : Placement) (o : Nat) (ho : o = 0) :
    zlibCrc32Text.patchedWord pl o =
      if pl.relax o then nopWord else adrpWord 0x90000000#32 (pl.base + BitVec.ofNat 64 o) (pl.ρ symTab) := by
  have hr : zlibCrc32Text.relocAt? o = some { off := o, kind := .adrpHi21, sym := symTab } := by
    subst ho <;> rfl
  have h1 : zlibCrc32Text.relaxableAt o = true := by subst ho <;> decide
  have h2 : (4 ≤ o) = False := by subst ho; simp
  have hw : zlibCrc32Text.wordAt o = 0x90000000#32 := by subst ho <;> rfl
  have hlk : lookup symTab zlibCrc32Text.symbols = none := by decide
  cases h : pl.relax o <;> subst ho <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h2, hr, hw,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, CodeBlock.target,
      CodeBlock.resolve, hlk, addSignedAddr, patchRelocWord, RelocKind.isGotOrTlsIe]

theorem pw_addTab (pl : Placement) (o : Nat) (ho : o = 0) :
    zlibCrc32Text.patchedWord pl (o + 4) =
      if pl.relax o then adrWord (adrTemplate 0x91000000#32) (pl.base + BitVec.ofNat 64 (o + 4)) (pl.ρ symTab)
      else lo12Word 0 0x91000000#32 (pl.ρ symTab) := by
  have hr : zlibCrc32Text.relocAt? (o + 4) = some { off := o + 4, kind := .addLo12, sym := symTab } := by
    subst ho <;> rfl
  have h1 : zlibCrc32Text.relaxableAt o = true := by subst ho <;> decide
  have h2 : zlibCrc32Text.relaxableAt (o + 4) = false := by subst ho <;> decide
  have hw : zlibCrc32Text.wordAt (o + 4) = 0x91000000#32 := by subst ho <;> rfl
  have hlk : lookup symTab zlibCrc32Text.symbols = none := by decide
  have h4 : (4 ≤ o + 4) = True := by simp
  cases h : pl.relax o <;> subst ho <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h2, hr, hw, h4,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, CodeBlock.target,
      CodeBlock.resolve, hlk, addSignedAddr, patchRelocWord, RelocKind.isGotOrTlsIe]

section words
variable (D : BitVec 64)

theorem wA_maskTab : adrpWordOff 0x90000000#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_31Tab : (adrpWordOff 0x90000000#32 D).getLsbD 31 = true := by
  simp [adrpWordOff]

theorem wA_rdTab : (adrpWordOff 0x90000000#32 D).extractLsb' 0 5 = 0#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_offTab (hlo : ∀ i, i < 12 → D.getLsbD i = false)
    (hhi : ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32) :
    ((adrpWordOff 0x90000000#32 D).extractLsb' 5 19 ++
      (adrpWordOff 0x90000000#32 D).extractLsb' 29 2).signExtend 64 <<< 12 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getMsbD]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm

theorem wC_maskTab : adrWordOff 0x10000000#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_31Tab : (adrWordOff 0x10000000#32 D).getLsbD 31 = false := by
  simp [adrWordOff]

theorem wC_rdTab : (adrWordOff 0x10000000#32 D).extractLsb' 0 5 = 0#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_offTab (hhi : ∀ i, 20 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 20) :
    ((adrWordOff 0x10000000#32 D).extractLsb' 5 19 ++
      (adrWordOff 0x10000000#32 D).extractLsb' 29 2).signExtend 64 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | rfl | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm

theorem wB_maskTab : lo12Word 0 0x91000000#32 D &&& 0x1f800000#32 = 0x11000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wB_bitsTab : (lo12Word 0 0x91000000#32 D).getLsbD 31 = true ∧
    (lo12Word 0 0x91000000#32 D).getLsbD 30 = false ∧
    (lo12Word 0 0x91000000#32 D).getLsbD 29 = false ∧
    (lo12Word 0 0x91000000#32 D).getLsbD 22 = false := by
  simp [lo12Word]

theorem wB_rdTab : (lo12Word 0 0x91000000#32 D).extractLsb' 0 5 = 0#5 ∧
    (lo12Word 0 0x91000000#32 D).extractLsb' 5 5 = 0#5 := by
  constructor <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem wB_immTab : (lo12Word 0 0x91000000#32 D).extractLsb' 10 12 = D.extractLsb' 0 12 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

end words

theorem decode_ATab {P T : BitVec 64} (hr : AdrpInRange P T) :
    decode (adrpWord 0x90000000#32 P T) = some (.adr true (.gpr 0#5) (pageOf T - pageOf P)) := by
  rw [adrpWord, decode_adr_class _ (wA_maskTab _), wA_31Tab, wA_rdTab,
    wA_offTab _ (lo_bits T P) (hi_bits32 _ hr.1 hr.2)]
  rfl

theorem decode_CTab {P T : BitVec 64} (hr : AdrInRange P T) :
    decode (adrWord (adrTemplate 0x91000000#32) P T) = some (.adr false (.gpr 0#5) (T - P)) := by
  rw [adrWord, show adrTemplate 0x91000000#32 = 0x10000000#32 by decide,
    decode_adr_class _ (wC_maskTab _), wC_31Tab, wC_rdTab, if_neg (by decide), wC_offTab _ (hi_bits20 _ hr.1 hr.2)]
  rfl

theorem decode_BTab (T : BitVec 64) :
    decode (lo12Word 0 0x91000000#32 T) =
      some (.addSubImm .W64 .ADD (.gpr 0#5) (.gpr 0#5) (T.extractLsb' 0 12) false) := by
  obtain ⟨b31, b30, b29, b22⟩ := wB_bitsTab T
  rw [decode_addimm_class _ (wB_maskTab _), b31, b30, b29, b22, wB_rdTab T |>.1, wB_rdTab T |>.2, wB_immTab]
  rfl

theorem targetTab (pl : Placement) (o : Nat) (k : RelocKind) :
    zlibCrc32Text.target pl { off := o, kind := k, sym := symTab } = pl.ρ symTab := by
  have hlk : lookup symTab zlibCrc32Text.symbols = none := by decide
  simp [CodeBlock.target, CodeBlock.resolve, hlk, addSignedAddr]

theorem range_adrpTab {pl : Placement} (hP : zlibCrc32Lib.Placeable pl) (o : Nat) (ho : o = 0) :
    AdrpInRange (pl.base + BitVec.ofNat 64 o) (pl.ρ symTab) := by
  have hmem : ({ off := o, kind := .adrpHi21, sym := symTab } : RelocEntry) ∈ zlibCrc32Text.relocs := by
    subst ho <;> decide
  have h := (hP.text.relocs_ok _ hmem).2.2
  have ht : zlibCrc32Text.relocTarget pl o { off := o, kind := .adrpHi21, sym := symTab } = pl.ρ symTab := by
    simp only [CodeBlock.relocTarget, CodeBlock.b2bNext?]
    simp [targetTab]
  simp only [zlibCrc32Lib] at h
  rw [ht] at h
  exact h

theorem range_adrTab {pl : Placement} (hP : zlibCrc32Lib.Placeable pl) (o : Nat) (ho : o = 0)
    (hrel : pl.relax o = true) :
    AdrInRange (pl.base + BitVec.ofNat 64 (o + 4)) (pl.ρ symTab) := by
  have h1 : zlibCrc32Text.relaxableAt o = true := by subst ho <;> decide
  have hr : zlibCrc32Text.relocAt? (o + 4) = some { off := o + 4, kind := .addLo12, sym := symTab } := by
    subst ho <;> rfl
  have hPt : zlibCrc32Text.Placeable pl := hP.text
  have h := hPt.relaxed_ok o _ (by simp [CodeBlock.relaxedAt, h1, hrel]) hr
  rwa [targetTab] at h

/-- Both forms of the pair load the object's address into `x0`. -/
theorem steps_pairTab {pl : Placement} {s0 : State} {r : BitVec 5 → BitVec 64} {ps : PState}
    (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded s0.mem)
    (hrun : s0.status = .Running) (o : Nat) (ho : o = 0) :
    Steps (prog pl) (mkS s0 (pl.base + BitVec.ofNat 64 o) r ps)
      (mkS s0 (pl.base + BitVec.ofNat 64 (o + 8)) (Function.update r 0#5 (pl.ρ symTab)) ps) := by
  have hal : o % 4 = 0 := by subst ho <;> rfl
  have hle : o + 8 ≤ 2824 := by subst ho <;> decide
  have hf2 := fetch_word hP hCL (off := o + 4) (by omega) (by omega)
  rw [pw_addTab pl o ho] at hf2
  have hf1 := fetch_word hP hCL (off := o) hal (by omega)
  rw [pw_adrpTab pl o ho] at hf1
  have p4 : pl.base + BitVec.ofNat 64 o + 4#64 = pl.base + BitVec.ofNat 64 (o + 4) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have p8 : pl.base + BitVec.ofNat 64 (o + 4) + 4#64 = pl.base + BitVec.ofNat 64 (o + 8) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show o + 4 + 4 = o + 8 by omega]
  have hrd : (0#5 : BitVec 5) ≠ 31#5 := by decide
  cases h : pl.relax o
  · simp only [h, Bool.false_eq_true, if_false] at hf1 hf2
    rw [decode_ATab (range_adrpTab hP o ho)] at hf1
    rw [decode_BTab] at hf2
    have st1 := step_mkS (r := r) (ps := ps) hrun hf1
    have e1 : execInstWithSvc (evalSvc Syscall.standard)
        (.adr true (.gpr 0#5) (pageOf (pl.ρ symTab) - pageOf (pl.base + BitVec.ofNat 64 o)))
        (mkS s0 (pl.base + BitVec.ofNat 64 o) r ps) =
        mkS s0 (pl.base + BitVec.ofNat 64 (o + 4)) (Function.update r 0#5 (pageOf (pl.ρ symTab))) ps := by
      show State.advancePC (State.writeReg64 _ _ _) = _
      rw [wr_gpr _ _ _ _ _ _ hrd, mkS_advancePC, p4]
      congr 2
      have e : ∀ a b : BitVec 64, a + (b - a) = b := by intro a b; bv_omega
      simp only [mkS_pc, if_true]
      rw [show (pl.base + BitVec.ofNat 64 o) &&& 0xfffffffffffff000#64 =
        pageOf (pl.base + BitVec.ofNat 64 o) from rfl, e]
    rw [e1] at st1
    have st2 := step_mkS (r := Function.update r 0#5 (pageOf (pl.ρ symTab))) (ps := ps) hrun hf2
    have e2 : execInstWithSvc (evalSvc Syscall.standard)
        (.addSubImm .W64 .ADD (.gpr 0#5) (.gpr 0#5) ((pl.ρ symTab).extractLsb' 0 12) false)
        (mkS s0 (pl.base + BitVec.ofNat 64 (o + 4)) (Function.update r 0#5 (pageOf (pl.ρ symTab))) ps) =
        mkS s0 (pl.base + BitVec.ofNat 64 (o + 8)) (Function.update r 0#5 (pl.ρ symTab)) ps := by
      show State.advancePC (State.writeReg _ _ _ _) = _
      simp only [State.writeReg, State.readReg, rd_gpr, hrd, if_false, Function.update_self,
        evalAddSub, Bool.false_eq_true]
      rw [wr_gpr _ _ _ _ _ _ hrd, mkS_advancePC, p8, Function.update_idem]
      congr 2
      rw [awc_add']
      exact page_add_lo _
    rw [e2] at st2
    exact Steps.step st1 (Steps.step st2 (Steps.refl _))
  · simp only [h, if_true] at hf1 hf2
    rw [decode_nop] at hf1
    rw [decode_CTab (range_adrTab hP o ho h)] at hf2
    have st1 := step_mkS (r := r) (ps := ps) hrun hf1
    rw [show execInstWithSvc (evalSvc Syscall.standard) .nop (mkS s0 (pl.base + BitVec.ofNat 64 o) r ps) =
      mkS s0 (pl.base + BitVec.ofNat 64 o + 4#64) r ps from rfl, p4] at st1
    have st2 := step_mkS (r := r) (ps := ps) hrun hf2
    have e2 : execInstWithSvc (evalSvc Syscall.standard)
        (.adr false (.gpr 0#5) (pl.ρ symTab - (pl.base + BitVec.ofNat 64 (o + 4))))
        (mkS s0 (pl.base + BitVec.ofNat 64 (o + 4)) r ps) =
        mkS s0 (pl.base + BitVec.ofNat 64 (o + 8)) (Function.update r 0#5 (pl.ρ symTab)) ps := by
      show State.advancePC (State.writeReg64 _ _ _) = _
      rw [wr_gpr _ _ _ _ _ _ hrd, mkS_advancePC, p8]
      congr 2
      simp only [mkS_pc, Bool.false_eq_true, if_false]
      bv_omega
    rw [e2] at st2
    exact Steps.step st1 (Steps.step st2 (Steps.refl _))

end ZlibCrc32.Small
end

section
/-! # Memory facts from the preconditions; read-only points-to is duplicable -/

namespace ZlibCrc32.Small

open Arm64 Arm64.Obj

theorem dataInit_eq (pl : Placement) :
    zlibCrc32Lib.dataInit pl =
      (pointsToBytesRO (pl.ρ "crc_table [zlib_crc32]") zlibCrc32PlacedData0 ∗
        (pointsToBytesRO (pl.ρ "crc_braid_table [zlib_crc32]") zlibCrc32PlacedData1 ∗
          pointsToBytesRO (pl.ρ "x2n_table [zlib_crc32]") zlibCrc32PlacedData2)) := by
  simp only [PlacedLib.dataInit, zlibCrc32Lib, zlibCrc32Data, List.map, sepAll,
    PlacedLib.patchedData, List.foldl, List.replicate, List.append_nil, if_true]

/-! ## Ghost-free read-only heaps -/

/-- A heap of read-only cells with no ghost state and no mapping tokens. -/
def ROHeap (h : Heap) : Prop :=
  (∀ a c, h.phys a = some c → ∃ b, c = .ro b) ∧ (∀ γ k, h.auth γ k = none) ∧
    (∀ γ k, h.frag γ k = none) ∧ (∀ a, h.mapped a = false)

theorem roHeap_bytes : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap),
    (pointsToBytesRO a bs).holds h → ROHeap h
  | [], _, h, hs => by
    simp only [pointsToBytesRO] at hs
    change h = Heap.empty at hs
    subst hs
    refine ⟨fun a c hc => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
    simp [Heap.empty] at hc
  | b :: bs, a, h, hs => by
    simp only [pointsToBytesRO] at hs
    obtain ⟨h1, h2, _, rfl, p1, p2⟩ := hs
    simp only [pointsTo8RO] at p1
    subst p1
    obtain ⟨q1, q2, q3, q4⟩ := roHeap_bytes bs _ h2 p2
    refine ⟨fun x c hc => ?_, fun γ k => ?_, fun γ k => ?_, fun x => ?_⟩
    · simp only [Heap.union, Heap.singletonRO] at hc
      split_ifs at hc with hx
      · cases hc; exact ⟨_, rfl⟩
      · exact q1 x c hc
    · simp [Heap.union, Heap.singletonRO, q2]
    · simp [Heap.union, Heap.singletonRO, q3]
    · simp [Heap.union, Heap.singletonRO, q4]

theorem union_self_left (h1 h2 : Heap) : h1.union (h1.union h2) = h1.union h2 := by
  cases h1; cases h2
  simp only [Heap.union, Heap.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext a; split <;> simp_all
  · funext γ k; split <;> simp_all
  · funext γ k; split <;> simp_all
  · funext a; cases ‹BitVec 64 → Bool› a <;> simp

theorem disjoint_self_union {h1 : Heap} (hr : ROHeap h1) (h2 : Heap) : h1.Disjoint (h1.union h2) := by
  obtain ⟨q1, q2, q3, q4⟩ := hr
  refine ⟨fun a => ?_, fun γ k => Or.inl (q2 γ k), fun γ k => Or.inl (q3 γ k), ?_,
    fun a => Or.inl (q4 a)⟩
  · cases hc : h1.phys a with
    | none => exact Or.inl rfl
    | some c =>
      obtain ⟨b, rfl⟩ := q1 a c hc
      exact Or.inr (Or.inr ⟨b, rfl, by simp [Heap.union, hc]⟩)
  · intro γ k oa v h
    rcases h with ⟨h, _⟩ | ⟨_, h⟩
    · rw [q2] at h; cases h
    · rw [q3] at h; cases h

/-- A ghost-free read-only assertion can be duplicated. -/
theorem sep_dup {P Q : SepProp} (hP : ∀ h, P.holds h → ROHeap h) {h : Heap}
    (hs : (P ∗ Q).holds h) : (P ∗ (P ∗ Q)).holds h := by
  obtain ⟨h1, h2, hd, rfl, p1, q2⟩ := hs
  exact ⟨h1, h1.union h2, disjoint_self_union (hP h1 p1) h2, (union_self_left h1 h2).symm, p1,
    ⟨h1, h2, hd, rfl, p1, q2⟩⟩

theorem empty_union (h : Heap) : Heap.empty.union h = h := by
  cases h; simp [Heap.union, Heap.empty]

theorem disjoint_empty (h : Heap) : Heap.empty.Disjoint h := by
  refine ⟨fun a => Or.inl rfl, fun γ k => Or.inl rfl, fun γ k => Or.inl rfl, ?_, fun a => Or.inl rfl⟩
  intro γ k oa v h
  rcases h with ⟨h, _⟩ | ⟨_, h⟩ <;> cases h

theorem pure_sep {φ : Prop} {P : SepProp} {h : Heap} (hφ : φ) (hP : P.holds h) :
    (⌜φ⌝ ∗ P).holds h :=
  ⟨Heap.empty, h, disjoint_empty h, (empty_union h).symm, ⟨rfl, hφ⟩, hP⟩

end ZlibCrc32.Small
end

section
/-! # `get_crc_table` returns the address of `crc_table` -/

namespace ZlibCrc32.Small

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

theorem fnAddr_get_crc_table (pl : Placement) :
    zlibCrc32Lib.fnAddr pl "get_crc_table" = pl.base + BitVec.ofNat 64 0 := rfl

theorem f_gct_8 {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded m) :
    (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 8) = some (.ret (.gpr 30#5)) :=
  fetch_plain hP hCL (by decide) (by decide) (by rfl) (by rfl)

/-- The final state of `get_crc_table`. -/
def gctFinal (pl : Placement) (s0 : State) : State :=
  mkS s0 (s0.regs.regs 30#5) (Function.update s0.regs.regs 0#5 (pl.ρ symTab)) s0.pstate

theorem steps_gct {pl : Placement} {s0 : State} (hP : zlibCrc32Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded s0.mem) (hrun : s0.status = .Running)
    (hpc : s0.pc = pl.base + BitVec.ofNat 64 0) : Steps (prog pl) s0 (gctFinal pl s0) := by
  have e0 : s0 = mkS s0 (pl.base + BitVec.ofNat 64 0) s0.regs.regs s0.pstate := by
    rw [← hpc]; rfl
  have h1 := steps_pairTab (r := s0.regs.regs) (ps := s0.pstate) hP hCL hrun 0 rfl
  have st := step_mkS (r := Function.update s0.regs.regs 0#5 (pl.ρ symTab)) (ps := s0.pstate)
    hrun (f_gct_8 hP hCL)
  rw [ex_ret, Function.update_of_ne (by decide)] at st
  rw [e0]
  exact Steps.trans' h1 (Steps.step st (Steps.refl _))

/-- `get_crc_table` meets its contract, given the table statement. -/
theorem get_crc_table_ok (ht : (zlibCrc32PlacedData0.length = 1024 ∧ ∀ i < 256,
      KadatchJenkins.regPoly (word32 zlibCrc32PlacedData0 i) =
        KadatchJenkins.crc0 crc32P (KadatchJenkins.Message.ofBytes [BitVec.ofNat 8 i]) 0)) :
    zlibCrc32Lib.subroutineOk "get_crc_table" getCrcTableSpec := by
  refine ⟨by decide, ?_⟩
  intro pl hP g R s0 hpc hrun hpre hal hCL
  change (prog pl).CodeLoaded s0.mem at hCL
  rw [fnAddr_get_crc_table] at hpc
  refine ⟨gctFinal pl s0, steps_gct hP hCL hrun hpc, Or.inl ⟨⟨rfl, rfl, hrun⟩, ⟨rfl, ?_⟩, ?_⟩⟩
  · simp [CalleeSavedPreserved, gctFinal, State.readReg64, mkS, RegFile.read, Function.update_apply]
  · obtain ⟨h, ⟨h1, h2, hd, rfl, hD, hR⟩, hm⟩ := hpre
    refine ⟨h1.union h2, ⟨h1, h2, hd, rfl, ?_, hR⟩, hm⟩
    have hx0 : (gctFinal pl s0).readReg64 Reg.x0 = pl.ρ "crc_table [zlib_crc32]" := rfl
    simp only [getCrcTableSpec]
    refine pure_sep hx0 ?_
    change (zlibCrc32Lib.dataInit pl).holds h1 at hD
    rw [dataInit_eq] at hD ⊢
    obtain ⟨hA, hAB, hd', heq, pA, pAB⟩ := sep_dup (fun h hh => roHeap_bytes _ _ h hh) hD
    refine ⟨hA, hAB, hd', heq, ⟨zlibCrc32PlacedData0, pure_sep ht ?_⟩, pAB⟩
    rw [hx0]; exact pA

end ZlibCrc32.Small
end

open ZlibCrc32 in
theorem solution : zlibCrc32Lib.subroutineOk "get_crc_table" getCrcTableSpec :=
  ZlibCrc32.Small.get_crc_table_ok crc_tables_eq.1
