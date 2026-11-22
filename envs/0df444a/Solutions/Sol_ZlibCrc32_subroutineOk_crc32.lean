-- Prove2me | solution 1 for ZlibCrc32.subroutineOk_crc32
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T10:31:08.345576+00:00
-- url     : https://prove2.me/submissions/fdbc3891-1c18-4b95-8605-a3daee245a2a

import Mathlib.Tactic.IntervalCases
import Definitions.Def_ZlibCrc32_Spec
import Theorems.Thm_ZlibCrc32_subroutineOk_crc32_z

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

/-- `MOV Wd, Wn` (`ORR Wd, WZR, Wn`). -/
theorem ex_movw {d n : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W32 .ORR (.gpr d) .xzr (.gpr n) .LSL 0) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) (Function.update r d (W (lo (r n)))) ps := by
  show (State.writeReg _ _ _ _).advancePC = _
  simp only [State.writeReg, State.readReg, State.readReg32, rd_gpr, hn, if_false,
    wr_gpr _ _ _ _ _ _ hd, mkS_advancePC, evalLogical, shiftVal, shift32, rd_xzr]
  congr 3
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem ex_b {off : BitVec 64} :
    execInstWithSvc svc (.b off) (mkS s0 pc r ps) = mkS s0 (pc + off) r ps := rfl

end exec

end ZlibCrc32.Small
end

section
/-! # `crc32` zero-extends `len` and tail-calls `crc32_z` -/

namespace ZlibCrc32.Small

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

theorem f_crc32_0 {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded m) :
    (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 2044) =
      some (.logicalShift .W32 .ORR (.gpr 2#5) .xzr (.gpr 2#5) .LSL 0) :=
  fetch_plain hP hCL (by decide) (by decide) (by rfl) (by rfl)

/-- The relocated `B crc32_z` at offset 2048: the displacement is `12 - 2048` under every
placement. -/
theorem pw_crc32_b (pl : Placement) : zlibCrc32Text.patchedWord pl 2048 = 0x17fffe03#32 := by
  have hr : zlibCrc32Text.relocAt? 2048 = some { off := 2048, kind := .jump26, sym := "crc32_z" } := by
    rfl
  have h1 : zlibCrc32Text.relaxableAt 2048 = false := by decide
  have h2 : zlibCrc32Text.relaxableAt 2044 = false := by decide
  have hb : zlibCrc32Text.b2bNext? { off := 2048, kind := .jump26, sym := "crc32_z" } = none := by
    decide
  have hw : zlibCrc32Text.wordAt 2048 = 0x14000000#32 := by rfl
  have hlk : lookup "crc32_z" zlibCrc32Text.symbols = some 12 := by decide
  have hwk : zlibCrc32Text.undefWeakBranch pl { off := 2048, kind := .jump26, sym := "crc32_z" } = false := by
    simp [CodeBlock.undefWeakBranch, zlibCrc32Text]
  have hd : pl.base + BitVec.ofNat 64 12 - (pl.base + BitVec.ofNat 64 2048) = 0xfffffffffffff80c#64 := by
    bv_omega
  cases h : pl.b2b 2048 <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h2, hr, hw, hb, hwk,
      CodeBlock.relocTarget, CodeBlock.target, CodeBlock.resolve, hlk, addSignedAddr,
      patchRelocWord, RelocKind.isGotOrTlsIe, branchWord, hd]

theorem f_crc32_4 {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded m) :
    (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 2048) = some (.b 0xfffffffffffff80c#64) := by
  rw [fetch_word hP hCL (by decide) (by decide), pw_crc32_b]; rfl

theorem fnAddr_crc32 (pl : Placement) : zlibCrc32Lib.fnAddr pl "crc32" = pl.base + BitVec.ofNat 64 2044 :=
  rfl

theorem fnAddr_crc32_z (pl : Placement) : zlibCrc32Lib.fnAddr pl "crc32_z" = pl.base + BitVec.ofNat 64 12 :=
  rfl

/-- The state at `crc32_z`'s entry: `x2` zero-extended from its low 32 bits. -/
def s1 (pl : Placement) (s0 : State) : State :=
  mkS s0 (pl.base + BitVec.ofNat 64 12)
    (Function.update s0.regs.regs 2#5 (W (lo (s0.regs.regs 2#5)))) s0.pstate

theorem steps_s1 {pl : Placement} {s0 : State} (hP : zlibCrc32Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded s0.mem) (hrun : s0.status = .Running)
    (hpc : s0.pc = pl.base + BitVec.ofNat 64 2044) : Steps (prog pl) s0 (s1 pl s0) := by
  have e0 : s0 = mkS s0 (pl.base + BitVec.ofNat 64 2044) s0.regs.regs s0.pstate := by
    rw [← hpc]; rfl
  have st1 := step_mkS (r := s0.regs.regs) (ps := s0.pstate) hrun (f_crc32_0 hP hCL)
  rw [ex_movw (by decide) (by decide)] at st1
  have hpc2 : pl.base + BitVec.ofNat 64 2044 + 4#64 = pl.base + BitVec.ofNat 64 2048 := by
    rw [BitVec.add_assoc]; rfl
  rw [hpc2] at st1
  have st2 := step_mkS (r := Function.update s0.regs.regs 2#5 (W (lo (s0.regs.regs 2#5))))
    (ps := s0.pstate) hrun (f_crc32_4 hP hCL)
  rw [ex_b] at st2
  have hpc3 : pl.base + BitVec.ofNat 64 2048 + 0xfffffffffffff80c#64 = pl.base + BitVec.ofNat 64 12 := by
    rw [BitVec.add_assoc]; rfl
  rw [hpc3] at st2
  rw [e0]
  exact Steps.step st1 (Steps.step st2 (Steps.refl _))

theorem s1_x2 (pl : Placement) (s0 : State) :
    (s1 pl s0).readReg64 (.gpr 2#5) = W (lo (s0.readReg64 (.gpr 2#5))) := rfl

theorem pre_eq (pl : Placement) (s0 : State) (g : Option (List (BitVec 8))) :
    (crc32zSpec pl).pre g (s1 pl s0) = (crc32Spec pl).pre g s0 := by
  cases g with
  | none => rfl
  | some bs =>
    have h : ((s1 pl s0).readReg64 (.gpr 2#5)).toNat = ((s0.readReg64 (.gpr 2#5)).setWidth 32).toNat := by
      rw [s1_x2]; simp [W, lo]; omega
    simp only [crc32zSpec, crc32Spec, h]; rfl

theorem post_eq (pl : Placement) (s0 sf : State) (g : Option (List (BitVec 8))) :
    (crc32zSpec pl).post g (s1 pl s0) sf = (crc32Spec pl).post g s0 sf := by
  cases g <;> rfl

/-- `crc32` meets its contract, given `crc32_z`'s. -/
theorem crc32_ok (hz : zlibCrc32Lib.subroutineOk "crc32_z" crc32zSpec) :
    zlibCrc32Lib.subroutineOk "crc32" crc32Spec := by
  refine ⟨by decide, ?_⟩
  intro pl hP g R s0 hpc hrun hpre hal hCL
  change (prog pl).CodeLoaded s0.mem at hCL
  rw [fnAddr_crc32] at hpc
  have h1 := hz.2 pl hP g R (s1 pl s0) (fnAddr_crc32_z pl).symm hrun (by rw [pre_eq]; exact hpre) hal hCL
  obtain ⟨sf, hs, hout⟩ := h1
  refine ⟨sf, Steps.trans' (steps_s1 hP hCL hrun hpc) hs, ?_⟩
  rcases hout with ⟨⟨hr1, hr2, hr3⟩, ⟨hc1, hc2⟩, hpost⟩ | hpan | hex | hoom
  · left
    refine ⟨⟨hr1, hr2, hr3⟩, ⟨hc1, hc2⟩, ?_⟩
    rw [← post_eq]; exact hpost
  · right; left; exact hpan
  · right; right; left; exact hex
  · right; right; right; exact hoom

end ZlibCrc32.Small
end

open ZlibCrc32 in
theorem solution : zlibCrc32Lib.subroutineOk "crc32" crc32Spec :=
  ZlibCrc32.Small.crc32_ok subroutineOk_crc32_z
