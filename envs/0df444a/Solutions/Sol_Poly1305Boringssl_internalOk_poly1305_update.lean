-- Prove2me | solution 1 for Poly1305Boringssl.internalOk_poly1305_update
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-24T10:20:35.216405+00:00
-- url     : https://prove2.me/submissions/deb93be6-58e1-42ce-b9a2-2e02e6c0d6d0

import Mathlib.Tactic.IntervalCases
import Definitions.Def_Poly1305Boringssl_Spec
import Mathlib.Tactic.Ring

section
/-! # Instruction fetch for the placed `boringsslPoly1305` text block -/

namespace Poly1305Boringssl.Proof

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-- The placed program the goal talks about. -/
def prog (pl : Placement) : Program := boringsslPoly1305Lib.program pl (fun _ => none) (fun _ => none)

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
theorem code_length : boringsslPoly1305PlacedCode.length = 1136 := by rfl

theorem patched_length (pl : Placement) : (boringsslPoly1305Text.patched pl).length = 1136 := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE]
  show (List.map (fun _ => 4) (List.range (boringsslPoly1305PlacedCode.length / 4))).sum = 1136
  rw [code_length]; rfl

theorem hook_none (pl : Placement) (pc : BitVec 64) : (prog pl).externAt? pc = none := by
  simp [prog, Program.externAt?, Program.hookAtOff?, PlacedLib.program, boringsslPoly1305Lib, boringsslPoly1305Text]

/-- Byte `k < 4` of the word at aligned offset `off` of the placed code. -/
theorem read8_code {pl : Placement} {m : Memory} (hCL : (prog pl).CodeLoaded m) {off k : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 1136) (hk : k < 4) :
    m.read8 (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      (boringsslPoly1305Text.patchedWord pl off).extractLsb' (8 * k) 8 ∧
    m.perm (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
  have hl : (prog pl).code.length = 1136 := patched_length pl
  have h := codeLoaded_cell hCL (off + k) (by omega)
  have ha : pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
      (prog pl).base + BitVec.ofNat 64 (off + k) := by
    show _ = pl.base + _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [ha]
  refine ⟨?_, h.2⟩
  rw [h.1]
  have ht := take4_drop_patched (blk := boringsslPoly1305Text) (pl := pl) hal
    (by rw [show boringsslPoly1305Text.code = boringsslPoly1305PlacedCode from rfl, code_length]; exact hlen)
  have e1 : (prog pl).code[off + k]'(by omega) =
      (((boringsslPoly1305Text.patched pl).drop off).take 4)[k]'(by
        simp [List.length_take, List.length_drop, patched_length]; omega) := by
    simp only [List.getElem_take, List.getElem_drop]; rfl
  rw [e1]
  simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * k + i < 32 := by omega
  simp [hi, this]; omega

theorem fetch_word {pl : Placement} {m : Memory} (hP : boringsslPoly1305Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded m) {off : Nat} (hal : off % 4 = 0) (hlen : off + 4 ≤ 1136) :
    (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      decode (boringsslPoly1305Text.patchedWord pl off) := by
  have hb4 : pl.base.toNat % 4 = 0 := by
    have := hP.text.base_aligned; simpa [boringsslPoly1305Lib, boringsslPoly1305Text] using this
  have hnw : pl.base.toNat + 1136 ≤ 2 ^ 64 := by
    have := hP.text.no_wrap
    have hl : boringsslPoly1305Text.code.length = 1136 := code_length
    rw [show boringsslPoly1305Lib.text = boringsslPoly1305Text from rfl, hl] at this
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

end Poly1305Boringssl.Proof
end

section
/-! # Abstract machine states and single-step plumbing

Every state reached by `poly1305_update` is `mkS s0 pc sp m ps r`: the entry state `s0` with
`pc`, `sp`, memory `m`, flags `ps` and the registers `x1..x18` (given by `r k` for `1 ≤ k ≤ 18`)
replaced. `x0`, `x19..x30` and everything else stay those of `s0`. -/

namespace Poly1305Boringssl.Proof

open Arm64 Arm64.Obj

/-- Register `k ∈ [1, 18]` is a scratch register of the abstraction. -/
def Ok (i : BitVec 5) : Prop := 1 ≤ i.toNat ∧ i.toNat ≤ 18

instance (i : BitVec 5) : Decidable (Ok i) := inferInstanceAs (Decidable (_ ∧ _))

/-- Update of the scratch register function. -/
def upd (r : Nat → BitVec 64) (k : Nat) (v : BitVec 64) : Nat → BitVec 64 :=
  fun j => if j = k then v else r j

@[simp] theorem upd_same (r : Nat → BitVec 64) (k : Nat) (v : BitVec 64) : upd r k v k = v := by
  simp [upd]

theorem upd_ne (r : Nat → BitVec 64) {k j : Nat} (v : BitVec 64) (h : j ≠ k) : upd r k v j = r j := by
  simp [upd, h]

def mkRegs (rf : RegFile) (r : Nat → BitVec 64) : RegFile :=
  ⟨fun i => if 1 ≤ i.toNat ∧ i.toNat ≤ 18 then r i.toNat else rf.regs i⟩

/-- The abstract state. -/
def mkS (s0 : State) (pc sp : BitVec 64) (m : Memory) (ps : PState) (r : Nat → BitVec 64) : State :=
  { s0 with regs := mkRegs s0.regs r, pc := pc, sp := sp, mem := m, pstate := ps }

section lemmas
variable (s0 : State) (pc sp : BitVec 64) (m : Memory) (ps : PState) (r : Nat → BitVec 64)

@[simp] theorem mkS_mem : (mkS s0 pc sp m ps r).mem = m := rfl
@[simp] theorem mkS_pc : (mkS s0 pc sp m ps r).pc = pc := rfl
@[simp] theorem mkS_sp : (mkS s0 pc sp m ps r).sp = sp := rfl
@[simp] theorem mkS_status : (mkS s0 pc sp m ps r).status = s0.status := rfl
@[simp] theorem mkS_pstate : (mkS s0 pc sp m ps r).pstate = ps := rfl
@[simp] theorem mkS_vregs : (mkS s0 pc sp m ps r).vregs = s0.vregs := rfl

theorem rd_gpr (i : BitVec 5) (h : Ok i) : (mkS s0 pc sp m ps r).readReg64 (.gpr i) = r i.toNat := by
  have h31 : (i == 31#5) = false := by
    have : i ≠ 31#5 := by intro e; subst e; simp [Ok] at h
    simpa using this
  simp only [State.readReg64, h31, mkS, RegFile.read, mkRegs]
  simp [Ok] at h; simp [h]

theorem rd_hi (i : BitVec 5) (h : 18 < i.toNat) :
    (mkS s0 pc sp m ps r).readReg64 (.gpr i) = s0.readReg64 (.gpr i) := by
  simp only [State.readReg64, mkS, RegFile.read, mkRegs]
  have : ¬ (1 ≤ i.toNat ∧ i.toNat ≤ 18) := by omega
  simp [this]

@[simp] theorem rd_xzr : (mkS s0 pc sp m ps r).readReg64 .xzr = 0#64 := rfl
@[simp] theorem rd_sp : (mkS s0 pc sp m ps r).readReg64 .sp = sp := rfl

theorem wr_gpr (i : BitVec 5) (h : Ok i) (v : BitVec 64) :
    (mkS s0 pc sp m ps r).writeReg64 (.gpr i) v = mkS s0 pc sp m ps (upd r i.toNat v) := by
  have h31 : (i == 31#5) = false := by
    have : i ≠ 31#5 := by intro e; subst e; simp [Ok] at h
    simpa using this
  simp only [mkS, State.writeReg64, h31, mkRegs, RegFile.write]
  simp only [Bool.false_eq_true, if_false]
  congr 2; funext j
  by_cases hj : j = i
  · subst hj; simp [Ok] at h; simp [h, upd]
  · have : j.toNat ≠ i.toNat := fun e => hj (BitVec.eq_of_toNat_eq e)
    simp [hj, upd, this]

@[simp] theorem wr_xzr (v : BitVec 64) : (mkS s0 pc sp m ps r).writeReg64 .xzr v = mkS s0 pc sp m ps r := rfl
@[simp] theorem wr_sp (v : BitVec 64) : (mkS s0 pc sp m ps r).writeReg64 .sp v = mkS s0 pc v m ps r := rfl
@[simp] theorem mkS_advancePC : (mkS s0 pc sp m ps r).advancePC = mkS s0 (pc + 4#64) sp m ps r := rfl
@[simp] theorem mkS_setPC (q : BitVec 64) : (mkS s0 pc sp m ps r).setPC q = mkS s0 q sp m ps r := rfl
@[simp] theorem mkS_setPState (q : PState) : (mkS s0 pc sp m ps r).setPState q = mkS s0 pc sp m q r := rfl
@[simp] theorem mkS_setMem (q : Memory) : (mkS s0 pc sp m ps r).setMem q = mkS s0 pc sp q ps r := rfl

end lemmas

/-! ## Steps utilities -/

theorem step_mkS {pl : Placement} {s0 : State} {pc sp : BitVec 64} {m : Memory} {ps : PState}
    {r : Nat → BitVec 64} {inst : Instr} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some inst) {s' : State}
    (he : execInstWithSvc (evalSvc Syscall.standard) inst (mkS s0 pc sp m ps r) = s') :
    Step (prog pl) (mkS s0 pc sp m ps r) s' := by
  have := Step.exec (prog := prog pl) (s := mkS s0 pc sp m ps r) hrun hf
  rw [Program.evalInst] at this
  rwa [show (prog pl).svc = Syscall.standard from rfl, he] at this

end Poly1305Boringssl.Proof
end

section
/-! # Memory: byte writes, the written region, and the memory invariant `MemOk`

The routine writes only the accumulator bytes `[x0 + 36, x0 + 56)` and its stack frame
`[sp0 - 16, sp0)` (the region `W`). `MemOk s0 m`: every cell outside `W` is that of `s0.mem`, and
every byte of `W` is mapped read-write (not lazy-free, anonymity unchanged), as in `s0.mem`. -/

namespace Poly1305Boringssl.Proof

open Arm64 Arm64.Obj

section write8
variable (m : Memory) (a b : BitVec 64) (v : BitVec 8)

theorem read8_write8 : (m.write8 a v).read8 b = if b = a then v else m.read8 b := by
  by_cases h : b = a <;> simp [Memory.write8, Memory.read8, h]

theorem cells_write8_ne (h : b ≠ a) : (m.write8 a v).cells b = m.cells b := by
  simp [Memory.write8, h]

theorem perm_write8 : (m.write8 a v).perm b = m.perm b := by
  by_cases h : b = a
  · subst h
    rcases hc : m.cells b with _ | ⟨_ | p, x⟩ <;>
      simp [Memory.write8, Memory.perm, Memory.rawPerm, hc, Perm.rwx]
  · simp [Memory.perm, cells_write8_ne m a b v h]

theorem lazy_write8 : (m.write8 a v).isLazyFree b = if b = a then false else m.isLazyFree b := by
  by_cases h : b = a
  · subst h
    rcases hc : m.cells b with _ | ⟨_ | p, x⟩ <;>
      simp [Memory.write8, Memory.isLazyFree, Memory.rawPerm, hc, Perm.rwx]
  · simp [Memory.isLazyFree, cells_write8_ne m a b v h, h]

theorem anon_write8 : (m.write8 a v).isAnon b = m.isAnon b := by
  by_cases h : b = a
  · subst h
    rcases hc : m.cells b with _ | ⟨_ | p, x⟩ <;>
      simp [Memory.write8, Memory.isAnon, Memory.rawPerm, hc, Perm.rwx]
  · simp [Memory.isAnon, cells_write8_ne m a b v h]

end write8

/-- The state address `x0` of the entry state. -/
abbrev X0 (s0 : State) : BitVec 64 := s0.readReg64 (.gpr 0#5)

/-- The written region: accumulator bytes and stack frame. -/
def W (s0 : State) (a : BitVec 64) : Prop :=
  InRegion (X0 s0 + 36#64) 20 a ∨ InRegion (s0.sp - 16#64) 16 a

def MemOk (s0 : State) (m : Memory) : Prop :=
  (∀ a, ¬ W s0 a → m.cells a = s0.mem.cells a) ∧
  (∀ a, W s0 a → m.perm a = some Perm.rw ∧ m.isLazyFree a = false ∧
    m.isAnon a = s0.mem.isAnon a ∧ s0.mem.perm a = some Perm.rw)

theorem memOk_write8 {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} (ha : W s0 a)
    (v : BitVec 8) : MemOk s0 (m.write8 a v) := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have : b ≠ a := fun e => hb (e ▸ ha)
    rw [cells_write8_ne _ _ _ _ this]; exact hm.1 b hb
  · obtain ⟨h1, h2, h3, h4⟩ := hm.2 b hb
    refine ⟨by rw [perm_write8]; exact h1, ?_, by rw [anon_write8]; exact h3, h4⟩
    rw [lazy_write8]; split <;> simp_all

theorem read8_of_notW {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} (ha : ¬ W s0 a) :
    m.read8 a = s0.mem.read8 a := by
  simp [Memory.read8, hm.1 a ha]

theorem perm_of_notW {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} (ha : ¬ W s0 a) :
    m.perm a = s0.mem.perm a := by
  simp [Memory.perm, hm.1 a ha]

theorem lazy_of_notW {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} (ha : ¬ W s0 a) :
    m.isLazyFree a = s0.mem.isLazyFree a := by
  simp [Memory.isLazyFree, hm.1 a ha]

/-! ## Permission checks over ranges -/

theorem allPerm_of {m : Memory} {p : Option Perm → Bool} :
    ∀ (n : Nat) (a : BitVec 64), (∀ k < n, p (m.perm (a + BitVec.ofNat 64 k)) = true) →
      m.allPerm p a n = true
  | 0, _, _ => rfl
  | n + 1, a, h => by
    simp only [Memory.allPerm, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), allPerm_of n _ fun k hk => ?_⟩
    have := h (k + 1) (by omega)
    rwa [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm 1 k] at *

theorem allNoLazy_of {m : Memory} :
    ∀ (n : Nat) (a : BitVec 64), (∀ k < n, m.isLazyFree (a + BitVec.ofNat 64 k) = false) →
      m.allNoLazyFree a n = true
  | 0, _, _ => rfl
  | n + 1, a, h => by
    simp only [Memory.allNoLazyFree, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), allNoLazy_of n _ fun k hk => ?_⟩
    have := h (k + 1) (by omega)
    rwa [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm 1 k] at *

theorem canWrite_of {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} {n : Nat}
    (h : ∀ k < n, W s0 (a + BitVec.ofNat 64 k)) : m.canWrite a n = true :=
  allPerm_of n a fun k hk => by rw [(hm.2 _ (h k hk)).1]; rfl

theorem canRead_W {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} {n : Nat}
    (h : ∀ k < n, W s0 (a + BitVec.ofNat 64 k)) : m.canRead a n = true := by
  simp only [Memory.canRead, Bool.and_eq_true]
  exact ⟨allPerm_of n a fun k hk => by rw [(hm.2 _ (h k hk)).1]; rfl,
    allNoLazy_of n a fun k hk => (hm.2 _ (h k hk)).2.1⟩

/-- Readable in `s0.mem` and outside `W`: readable in `m`. -/
theorem canRead_notW {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} {n : Nat}
    (h : ∀ k < n, ¬ W s0 (a + BitVec.ofNat 64 k) ∧ (s0.mem.perm (a + BitVec.ofNat 64 k)).r = true ∧
      s0.mem.isLazyFree (a + BitVec.ofNat 64 k) = false) : m.canRead a n = true := by
  simp only [Memory.canRead, Bool.and_eq_true]
  exact ⟨allPerm_of n a fun k hk => by rw [perm_of_notW hm (h k hk).1]; exact (h k hk).2.1,
    allNoLazy_of n a fun k hk => by rw [lazy_of_notW hm (h k hk).1]; exact (h k hk).2.2⟩

/-! ## Code stays loaded -/

theorem codeLoaded_of {p : Program} {m0 m : Memory} (h : p.CodeLoaded m0)
    (hc : ∀ a, m0.perm a = some Perm.rx → m.cells a = m0.cells a) : p.CodeLoaded m := by
  unfold Program.CodeLoaded at h ⊢
  refine ⟨h.1, h.2.1, fun i hi => ?_⟩
  obtain ⟨e1, e2, e3⟩ := h.2.2 i hi
  have hcl := hc _ e2
  simp only [Memory.read8, Memory.perm, Memory.isLazyFree, hcl] at e1 e2 e3 ⊢
  exact ⟨e1, e2, e3⟩

/-- Everything the stepping lemmas need about memory `m`. -/
def Good (pl : Placement) (s0 : State) (m : Memory) : Prop :=
  boringsslPoly1305Lib.Placeable pl ∧ (prog pl).CodeLoaded s0.mem ∧ MemOk s0 m

theorem Good.codeLoaded {pl : Placement} {s0 : State} {m : Memory} (hg : Good pl s0 m) :
    (prog pl).CodeLoaded m :=
  codeLoaded_of hg.2.1 fun a ha => hg.2.2.1 a fun hw => by
    have := (hg.2.2.2 a hw).2.2.2; rw [ha] at this; cases this

theorem Good.write8 {pl : Placement} {s0 : State} {m : Memory} (hg : Good pl s0 m) {a : BitVec 64}
    (ha : W s0 a) (v : BitVec 8) : Good pl s0 (m.write8 a v) :=
  ⟨hg.1, hg.2.1, memOk_write8 hg.2.2 ha v⟩

end Poly1305Boringssl.Proof
end

section
/-! # The instruction at each address of `poly1305_update` (block offsets 0x16c..0x340)

Generated from `decode (wordAt off)`; each lemma is `rfl` after `fetch_word` and
`patchedWord_plain` (no relocation lies inside the block). -/

namespace Poly1305Boringssl.Proof

open Arm64 Arm64.Obj

set_option maxRecDepth 100000

theorem patchedWord_plain (pl : Placement) {off : Nat}
    (h : boringsslPoly1305Text.relocAt? off = none) :
    boringsslPoly1305Text.patchedWord pl off = boringsslPoly1305Text.wordAt off := by
  simp [CodeBlock.patchedWord, h]

section
variable {pl : Placement} {s0 : State} {m : Memory} (hg : Good pl s0 m)
include hg

theorem f_0 : (prog pl).fetchMem m (pl.base + 364#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.sp) (Arm64.Reg.sp) 0x010#12 false) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_4 : (prog pl).fetchMem m (pl.base + 368#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x02#5) 0x010#12 false) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_8 : (prog pl).fetchMem m (pl.base + 372#64) = some (Arm64.Instr.bCond (Arm64.CondCode.CC) 0x000000000000012c#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c : (prog pl).fetchMem m (pl.base + 376#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000024#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_10 : (prog pl).fetchMem m (pl.base + 380#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000002c#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_14 : (prog pl).fetchMem m (pl.base + 384#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.W32) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000034#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_18 : (prog pl).fetchMem m (pl.base + 388#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000000#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1c : (prog pl).fetchMem m (pl.base + 392#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x10#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000008#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_20 : (prog pl).fetchMem m (pl.base + 396#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x01#5) 0x010#12 false) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_24 : (prog pl).fetchMem m (pl.base + 400#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) 0x010#12 false) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_28 : (prog pl).fetchMem m (pl.base + 404#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 32) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_2c : (prog pl).fetchMem m (pl.base + 408#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) 0x03ffffff03ffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_30 : (prog pl).fetchMem m (pl.base + 412#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.ShiftType.LSL) 32) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_34 : (prog pl).fetchMem m (pl.base + 416#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x10#5) (Arm64.ShiftType.LSL) 32) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_38 : (prog pl).fetchMem m (pl.base + 420#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_3c : (prog pl).fetchMem m (pl.base + 424#64) = some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x11#5) 26 51) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_40 : (prog pl).fetchMem m (pl.base + 428#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x10#5) (Arm64.ShiftType.LSR) 8) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_44 : (prog pl).fetchMem m (pl.base + 432#64) = some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0e#5) 20 45) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_48 : (prog pl).fetchMem m (pl.base + 436#64) = some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0f#5) 14 39) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_4c : (prog pl).fetchMem m (pl.base + 440#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_50 : (prog pl).fetchMem m (pl.base + 444#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_54 : (prog pl).fetchMem m (pl.base + 448#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x0d#5) 0x0100#16 16) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_58 : (prog pl).fetchMem m (pl.base + 452#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_5c : (prog pl).fetchMem m (pl.base + 456#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_60 : (prog pl).fetchMem m (pl.base + 460#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W32) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000024#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_64 : (prog pl).fetchMem m (pl.base + 464#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W32) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000002c#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_68 : (prog pl).fetchMem m (pl.base + 468#64) = some (Arm64.Instr.str (Arm64.MemWidth.W32) (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000034#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_6c : (prog pl).fetchMem m (pl.base + 472#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_70 : (prog pl).fetchMem m (pl.base + 476#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x10#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000001c#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_74 : (prog pl).fetchMem m (pl.base + 480#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000014#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_78 : (prog pl).fetchMem m (pl.base + 484#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_7c : (prog pl).fetchMem m (pl.base + 488#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x02#5) 0x00f#12 false) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_80 : (prog pl).fetchMem m (pl.base + 492#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_84 : (prog pl).fetchMem m (pl.base + 496#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0d#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_88 : (prog pl).fetchMem m (pl.base + 500#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x11#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_8c : (prog pl).fetchMem m (pl.base + 504#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0d#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_90 : (prog pl).fetchMem m (pl.base + 508#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x11#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_94 : (prog pl).fetchMem m (pl.base + 512#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0d#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_98 : (prog pl).fetchMem m (pl.base + 516#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x11#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_9c : (prog pl).fetchMem m (pl.base + 520#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.W32) false (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000008#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a0 : (prog pl).fetchMem m (pl.base + 524#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a4 : (prog pl).fetchMem m (pl.base + 528#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0d#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a8 : (prog pl).fetchMem m (pl.base + 532#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x11#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_ac : (prog pl).fetchMem m (pl.base + 536#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x12#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b0 : (prog pl).fetchMem m (pl.base + 540#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x12#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b4 : (prog pl).fetchMem m (pl.base + 544#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.ShiftType.LSR) 26) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b8 : (prog pl).fetchMem m (pl.base + 548#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x12#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_bc : (prog pl).fetchMem m (pl.base + 552#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) 0x03ffffff03ffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c0 : (prog pl).fetchMem m (pl.base + 556#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c4 : (prog pl).fetchMem m (pl.base + 560#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x12#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c8 : (prog pl).fetchMem m (pl.base + 564#64) = some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x11#5) 26 63) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_cc : (prog pl).fetchMem m (pl.base + 568#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d0 : (prog pl).fetchMem m (pl.base + 572#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x06#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000000c#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d4 : (prog pl).fetchMem m (pl.base + 576#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x05#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d8 : (prog pl).fetchMem m (pl.base + 580#64) = some (Arm64.Instr.addSubExt (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x07#5) (Arm64.ExtendType.UXTW) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_dc : (prog pl).fetchMem m (pl.base + 584#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e0 : (prog pl).fetchMem m (pl.base + 588#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0c#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e4 : (prog pl).fetchMem m (pl.base + 592#64) = some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x10#5) 26 63) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e8 : (prog pl).fetchMem m (pl.base + 596#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0c#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_ec : (prog pl).fetchMem m (pl.base + 600#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0f#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f0 : (prog pl).fetchMem m (pl.base + 604#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0b#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f4 : (prog pl).fetchMem m (pl.base + 608#64) = some (Arm64.Instr.addSubExt (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x12#5) (Arm64.ExtendType.UXTW) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f8 : (prog pl).fetchMem m (pl.base + 612#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0a#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_fc : (prog pl).fetchMem m (pl.base + 616#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x10#5) 0x03ffffff03ffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_100 : (prog pl).fetchMem m (pl.base + 620#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_104 : (prog pl).fetchMem m (pl.base + 624#64) = some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0b#5) 26 63) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_108 : (prog pl).fetchMem m (pl.base + 628#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) 0x03ffffff03ffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_10c : (prog pl).fetchMem m (pl.base + 632#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W32) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000002c#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_110 : (prog pl).fetchMem m (pl.base + 636#64) = some (Arm64.Instr.addSubExt (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ExtendType.UXTW) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_114 : (prog pl).fetchMem m (pl.base + 640#64) = some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x08#5) 26 63) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_118 : (prog pl).fetchMem m (pl.base + 644#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x08#5) 0x03ffffff03ffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_11c : (prog pl).fetchMem m (pl.base + 648#64) = some (Arm64.Instr.str (Arm64.MemWidth.W32) (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000034#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_120 : (prog pl).fetchMem m (pl.base + 652#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 2) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_124 : (prog pl).fetchMem m (pl.base + 656#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x11#5) 0x03ffffff03ffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_128 : (prog pl).fetchMem m (pl.base + 660#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_12c : (prog pl).fetchMem m (pl.base + 664#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W32) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000024#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_130 : (prog pl).fetchMem m (pl.base + 668#64) = some (Arm64.Instr.bCond (Arm64.CondCode.HI) 0xfffffffffffffee8#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_134 : (prog pl).fetchMem m (pl.base + 672#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x02#5) 0x0000000000000098#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_138 : (prog pl).fetchMem m (pl.base + 676#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_13c : (prog pl).fetchMem m (pl.base + 680#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.sp) 0x000#12 false) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_140 : (prog pl).fetchMem m (pl.base + 684#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.RegOffset (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ExtendType.UXTX) 0)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_144 : (prog pl).fetchMem m (pl.base + 688#64) = some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.RegOffset (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ExtendType.UXTX) 0)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_148 : (prog pl).fetchMem m (pl.base + 692#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) 0x001#12 false) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_14c : (prog pl).fetchMem m (pl.base + 696#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_150 : (prog pl).fetchMem m (pl.base + 700#64) = some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0xfffffffffffffff0#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_154 : (prog pl).fetchMem m (pl.base + 704#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x08#5) 0x001#12 false) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_158 : (prog pl).fetchMem m (pl.base + 708#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.sp) 0x000#12 false) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_15c : (prog pl).fetchMem m (pl.base + 712#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x0a#5) 0x00d#12 false) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_160 : (prog pl).fetchMem m (pl.base + 716#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x0a#5) 0x0001#16 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_164 : (prog pl).fetchMem m (pl.base + 720#64) = some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.RegOffset (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ExtendType.UXTX) 0)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_168 : (prog pl).fetchMem m (pl.base + 724#64) = some (Arm64.Instr.bCond (Arm64.CondCode.HI) 0x0000000000000018#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_16c : (prog pl).fetchMem m (pl.base + 728#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) 0x0000000000000001#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_170 : (prog pl).fetchMem m (pl.base + 732#64) = some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.xzr) (Arm64.AddrMode.RegOffset (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ExtendType.UXTX) 0)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_174 : (prog pl).fetchMem m (pl.base + 736#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) 0x001#12 false) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_178 : (prog pl).fetchMem m (pl.base + 740#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x08#5) 0x00f#12 false) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_17c : (prog pl).fetchMem m (pl.base + 744#64) = some (Arm64.Instr.bCond (Arm64.CondCode.CC) 0xfffffffffffffff4#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_180 : (prog pl).fetchMem m (pl.base + 748#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000000#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_184 : (prog pl).fetchMem m (pl.base + 752#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000008#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_188 : (prog pl).fetchMem m (pl.base + 756#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000024#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_18c : (prog pl).fetchMem m (pl.base + 760#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 32) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_190 : (prog pl).fetchMem m (pl.base + 764#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.W32) false (Arm64.Reg.gpr 0x12#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000002c#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_194 : (prog pl).fetchMem m (pl.base + 768#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) 0x03ffffff03ffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_198 : (prog pl).fetchMem m (pl.base + 772#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.ShiftType.LSL) 32) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_19c : (prog pl).fetchMem m (pl.base + 776#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 32) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1a0 : (prog pl).fetchMem m (pl.base + 780#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1a4 : (prog pl).fetchMem m (pl.base + 784#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000030#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1a8 : (prog pl).fetchMem m (pl.base + 788#64) = some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0c#5) 26 51) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1ac : (prog pl).fetchMem m (pl.base + 792#64) = some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x09#5) 20 45) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1b0 : (prog pl).fetchMem m (pl.base + 796#64) = some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x0a#5) 14 39) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1b4 : (prog pl).fetchMem m (pl.base + 800#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1b8 : (prog pl).fetchMem m (pl.base + 804#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSR) 8) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1bc : (prog pl).fetchMem m (pl.base + 808#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1c0 : (prog pl).fetchMem m (pl.base + 812#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x12#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1c4 : (prog pl).fetchMem m (pl.base + 816#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x04#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1c8 : (prog pl).fetchMem m (pl.base + 820#64) = some (Arm64.Instr.b 0xfffffffffffffea4#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1cc : (prog pl).fetchMem m (pl.base + 824#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.sp) (Arm64.Reg.sp) 0x010#12 false) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1d0 : (prog pl).fetchMem m (pl.base + 828#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

end

end Poly1305Boringssl.Proof
end

section
/-! # One reachability lemma per instruction shape

`Reach pl Q s`: from `s` the placed program reaches a state satisfying `Q`. Each `r_*` lemma
reduces `Reach` at an abstract state to `Reach` at its successor. Register indices are generic
(`Ok` side conditions are discharged by `decide`). -/

namespace Poly1305Boringssl.Proof

open Arm64 Arm64.Obj

def Reach (pl : Placement) (Q : State → Prop) (s : State) : Prop :=
  ∃ sf, Steps (prog pl) s sf ∧ Q sf

theorem reach_step {pl : Placement} {Q : State → Prop} {s s' : State} (h : Step (prog pl) s s')
    (h' : Reach pl Q s') : Reach pl Q s := by
  obtain ⟨sf, h1, h2⟩ := h'
  exact ⟨sf, Steps.step h h1, h2⟩

theorem reach_done {pl : Placement} {Q : State → Prop} {s : State} (h : Q s) : Reach pl Q s :=
  ⟨s, Steps.refl _, h⟩

def subFlags (x y : BitVec 64) : PState := (AddWithCarry64 x (~~~y) true).2

theorem pc_add (b : BitVec 64) (x y : Nat) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y = b + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

section
variable (svc : State → State) (s : State)
theorem ex_cbz (w : RegWidth) (nz : Bool) (rt : Reg) (off : BitVec 64) :
    execInstWithSvc svc (.cbz w nz rt off) s =
      (let val := s.readReg w rt
       let cond := if nz then (val == 0#64) != true else val == 0#64
       if cond then s.setPC (s.pc + off) else s.advancePC) := rfl
theorem ex_addSubImm (w : RegWidth) (op : AddSubOp) (rd rn : Reg) (imm : BitVec 12) (sh : Bool) :
    execInstWithSvc svc (.addSubImm w op rd rn imm sh) s = execAddSubImm w op rd rn imm sh s := rfl
theorem ex_addSubShift (w : RegWidth) (op : AddSubOp) (rd rn rm : Reg) (sh : ShiftType) (a : Nat) :
    execInstWithSvc svc (.addSubShift w op rd rn rm sh a) s = execAddSubShift w op rd rn rm sh a s := rfl
theorem ex_addSubExt (w : RegWidth) (op : AddSubOp) (rd rn rm : Reg) (e : ExtendType) (a : Nat) :
    execInstWithSvc svc (.addSubExt w op rd rn rm e a) s = execAddSubExt w op rd rn rm e a s := rfl
theorem ex_logicalShift (w : RegWidth) (op : LogicalOp) (rd rn rm : Reg) (sh : ShiftType) (a : Nat) :
    execInstWithSvc svc (.logicalShift w op rd rn rm sh a) s = execLogicalShift w op rd rn rm sh a s := rfl
theorem ex_logicalImm (w : RegWidth) (op : LogicalOp) (rd rn : Reg) (mask : BitVec 64) :
    execInstWithSvc svc (.logicalImm w op rd rn mask) s = execLogicalImm w op rd rn mask s := rfl
theorem ex_bitfield (w : RegWidth) (op : BitfieldOp) (rd rn : Reg) (a b : Nat) :
    execInstWithSvc svc (.bitfield w op rd rn a b) s = execBitfield w op rd rn a b s := rfl
theorem ex_moveWide (w : RegWidth) (op : MoveWideOp) (rd : Reg) (imm : BitVec 16) (hw : Nat) :
    execInstWithSvc svc (.moveWide w op rd imm hw) s = execMoveWide w op rd imm hw s := rfl
theorem ex_dataProc3 (w : RegWidth) (op : DataProc3Op) (rd rn rm ra : Reg) :
    execInstWithSvc svc (.dataProc3 w op rd rn rm ra) s = execDataProc3 w op rd rn rm ra s := rfl
theorem ex_bCond (c : CondCode) (off : BitVec 64) :
    execInstWithSvc svc (.bCond c off) s =
      if ConditionHolds c s.pstate then s.setPC (s.pc + off) else s.advancePC := rfl
theorem ex_b (off : BitVec 64) : execInstWithSvc svc (.b off) s = s.setPC (s.pc + off) := rfl
theorem ex_ldr (w : RegWidth) (sz : MemWidth) (sg : Bool) (rt : Reg) (a : AddrMode) :
    execInstWithSvc svc (.ldr w sz sg rt a) s = execLdr w sz sg rt a s := rfl
theorem ex_str (sz : MemWidth) (rt : Reg) (a : AddrMode) :
    execInstWithSvc svc (.str sz rt a) s = execStr sz rt a s := rfl
theorem ex_ldp (w : RegWidth) (sg : Bool) (r1 r2 : Reg) (a : AddrMode) :
    execInstWithSvc svc (.ldp w sg r1 r2 a) s = execLdp w sg r1 r2 a s := rfl
theorem ex_stp (w : RegWidth) (r1 r2 : Reg) (a : AddrMode) :
    execInstWithSvc svc (.stp w r1 r2 a) s = execStp w r1 r2 a s := rfl
theorem ex_ret (rn : Reg) : execInstWithSvc svc (.ret rn) s = s.setPC (s.readReg64 rn) := rfl
end

theorem mkS_upd_congr {s0 : State} {pc sp : BitVec 64} {m : Memory} {ps : PState}
    {r : Nat → BitVec 64} {k : Nat} {v v' : BitVec 64} (h : v.toNat = v'.toNat) :
    mkS s0 pc sp m ps (upd r k v) = mkS s0 pc sp m ps (upd r k v') := by
  rw [BitVec.eq_of_toNat_eq h]

theorem mkS_sp_congr {s0 : State} {pc sp sp' : BitVec 64} {m : Memory} {ps : PState}
    {r : Nat → BitVec 64} (h : sp.toNat = sp'.toNat) :
    mkS s0 pc sp m ps r = mkS s0 pc sp' m ps r := by
  rw [BitVec.eq_of_toNat_eq h]

variable {pl : Placement} {Q : State → Prop} {s0 : State} {pc sp : BitVec 64} {m : Memory}
  {ps : PState} {r : Nat → BitVec 64}

/-! ## Arithmetic and logic -/

theorem r_subSp (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.addSubImm .W64 .SUB .sp .sp 0x010#12 false))
    (h : Reach pl Q (mkS s0 (pc + 4#64) (sp - 16#64) m ps r)) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_addSubImm]
  simp [State.readReg, State.writeReg, evalAddSub, AddWithCarry64]
  refine mkS_sp_congr ?_; simp; omega

theorem r_addSp (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.addSubImm .W64 .ADD .sp .sp 0x010#12 false))
    (h : Reach pl Q (mkS s0 (pc + 4#64) (sp + 16#64) m ps r)) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_addSubImm]
  simp [State.readReg, State.writeReg, evalAddSub, AddWithCarry64]
  refine mkS_sp_congr ?_; simp; omega

theorem r_cmpImm {n : BitVec 5} {imm : BitVec 12} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.addSubImm .W64 .SUBS .xzr (.gpr n) imm false))
    (hn : Ok n := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m (subFlags (r n.toNat) (imm.setWidth 64)) r)) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_addSubImm]
  simp [State.readReg, State.writeReg, evalAddSub, rd_gpr _ _ _ _ _ _ _ hn, subFlags]

theorem r_cmpReg {n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.addSubShift .W64 .SUBS .xzr (.gpr n) (.gpr k) .LSL 0))
    (hn : Ok n := by decide) (hk : Ok k := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m (subFlags (r n.toNat) (r k.toNat)) r)) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_addSubShift]
  simp [State.readReg, State.writeReg, evalAddSub, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    subFlags, shiftVal, shift64]

/-- `add/sub xd, xn, #imm` (64-bit, no flags). -/
theorem r_addImm {d n : BitVec 5} {imm : BitVec 12} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.addSubImm .W64 .ADD (.gpr d) (.gpr n) imm false))
    (hd : Ok d := by decide) (hn : Ok n := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (r n.toNat + imm.setWidth 64)))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_addSubImm]
  simp only [execAddSubImm, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, evalAddSub, State.writeReg,
    wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC, Bool.false_eq_true, if_false]
  congr 2; simp [AddWithCarry64]
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem r_subImm {d n : BitVec 5} {imm : BitVec 12} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.addSubImm .W64 .SUB (.gpr d) (.gpr n) imm false))
    (hd : Ok d := by decide) (hn : Ok n := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (r n.toNat - imm.setWidth 64)))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_addSubImm]
  simp only [execAddSubImm, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, evalAddSub, State.writeReg,
    wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC, Bool.false_eq_true, if_false]
  congr 2; simp [AddWithCarry64]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

/-- `mov xd, sp`. -/
theorem r_movSp {d : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.addSubImm .W64 .ADD (.gpr d) .sp 0x000#12 false))
    (hd : Ok d := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat sp))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_addSubImm]
  simp only [execAddSubImm, State.readReg, rd_sp, evalAddSub, State.writeReg,
    wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC, Bool.false_eq_true, if_false]
  congr 2; simp [AddWithCarry64]

/-- `mov xd, xzr` (`orr xd, xzr, xzr`). -/
theorem r_movZero {d : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.logicalShift .W64 .ORR (.gpr d) .xzr .xzr .LSL 0))
    (hd : Ok d := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat 0#64))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_logicalShift]
  simp [State.readReg, evalLogical, State.writeReg, wr_gpr _ _ _ _ _ _ _ hd, shiftVal, shift64]

theorem orr_lsl32_toNat (x y : BitVec 64) (hx : x.toNat < 2 ^ 32) :
    (x ||| y <<< 32).toNat = x.toNat + 2 ^ 32 * (y.toNat % 2 ^ 32) := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.or_comm]
  have e : y.toNat <<< 32 % 2 ^ 64 = (y.toNat % 2 ^ 32) <<< 32 := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq,
      show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by norm_num, Nat.mul_mod_mul_right]
  rw [e, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  omega

/-- `orr xd, xn, xm, lsl #32` with `xn < 2^32`. -/
theorem r_orrLsl32 {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.logicalShift .W64 .ORR (.gpr d) (.gpr n) (.gpr k) .LSL 32))
    (hlt : (r n.toNat).toNat < 2 ^ 32)
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat
      (BitVec.ofNat 64 ((r n.toNat).toNat + 2 ^ 32 * ((r k.toNat).toNat % 2 ^ 32)))))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_logicalShift]
  simp only [execLogicalShift, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalLogical, State.writeReg, shiftVal, shift64]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  refine mkS_upd_congr ?_
  simp only [Nat.reduceMod]
  rw [orr_lsl32_toNat _ _ hlt, BitVec.toNat_ofNat]
  have := (r k.toNat).toNat.mod_lt (show 0 < 2 ^ 32 by decide)
  omega

/-- `orr xd, xn, #1`. -/
theorem r_orr1 {d n : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.logicalImm .W64 .ORR (.gpr d) (.gpr n) 0x0000000000000001#64))
    (hd : Ok d := by decide) (hn : Ok n := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (r n.toNat ||| 1#64)))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_logicalImm]
  simp [State.readReg, evalLogical, State.writeReg, rd_gpr _ _ _ _ _ _ _ hn, wr_gpr _ _ _ _ _ _ _ hd]

/-- `and wd, wn, #0x3ffffff`. -/
theorem r_andMask {d n : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.logicalImm .W32 .AND (.gpr d) (.gpr n) 0x03ffffff03ffffff#64))
    (hd : Ok d := by decide) (hn : Ok n := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat % 2 ^ 26))))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_logicalImm]
  simp [State.readReg, rd_gpr _ _ _ _ _ _ _ hn, evalLogical, State.writeReg,
    State.readReg32, wr_gpr _ _ _ _ _ _ _ hd]
  refine mkS_upd_congr ?_
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have hl := (r n.toNat).isLt
  rw [show (67108863 : Nat) % 2 ^ 64 = 2 ^ 26 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `ubfx xd, xn, #lsb, #26`. -/
theorem r_ubfx {d n : BitVec 5} {lsb hi : Nat} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.bitfield .W64 .UBFM (.gpr d) (.gpr n) lsb hi))
    (hl : lsb < 64 ∧ hi = lsb + 25 ∧ hi < 63 := by decide)
    (hd : Ok d := by decide) (hn : Ok n := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat / 2 ^ lsb % 2 ^ 26))))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  obtain ⟨h1, rfl, h3⟩ := hl
  rw [ex_bitfield]
  simp only [execBitfield, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, evalBitfield, State.writeReg]
  have e1 : (lsb + 25) % 64 = lsb + 25 := Nat.mod_eq_of_lt (by omega)
  have e2 : lsb % 64 = lsb := Nat.mod_eq_of_lt (by omega)
  simp only [e1, e2, wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  have c1 : (lsb + 25 + 1 == 64) = false := by simp; omega
  have c2 : ¬ (lsb > lsb + 25) := by omega
  simp [c1, c2]
  refine mkS_upd_congr ?_
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [show (67108863 : Nat) % 2 ^ 64 = 2 ^ 26 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.mod_lt ((r n.toNat).toNat / 2 ^ lsb) (show 0 < 67108864 by decide)
  omega

/-- `lsr xd, xn, #26`. -/
theorem r_lsr26 {d n : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.bitfield .W64 .UBFM (.gpr d) (.gpr n) 26 63))
    (hd : Ok d := by decide) (hn : Ok n := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat / 2 ^ 26))))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_bitfield]
  simp only [execBitfield, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, evalBitfield, State.writeReg]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  simp only [Nat.reduceMod, Nat.reduceAdd, beq_self_eq_true, Bool.and_self, if_true,
    show (BitfieldOp.UBFM == BitfieldOp.UBFM) = true from rfl]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := (r n.toNat).isLt
  rw [Nat.mod_eq_of_lt (by omega)]

/-- `add wd, wn, wm, <shift>` (32-bit): the shifted operand value is `f (wm)`. -/
theorem r_add32 {d n k : BitVec 5} {sh : ShiftType} {a : Nat} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.addSubShift .W32 .ADD (.gpr d) (.gpr n) (.gpr k) sh a))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 (((r n.toNat).toNat % 2 ^ 32 +
        (shift32 ((r k.toNat).setWidth 32) sh a).toNat) % 2 ^ 32))))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_addSubShift]
  simp only [execAddSubShift, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalAddSub, State.writeReg, State.readReg32, shiftVal]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC, Bool.false_eq_true, if_false]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry32, BitVec.toNat_setWidth, BitVec.toNat_add]
  omega

/-- `add xd, xn, xm, lsr #26`. -/
theorem r_add64lsr26 {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSR 26))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + (r k.toNat).toNat / 2 ^ 26))))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_addSubShift]
  simp only [execAddSubShift, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalAddSub, State.writeReg, shiftVal, shift64]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC, Bool.false_eq_true, if_false]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth, BitVec.toNat_add, Nat.shiftRight_eq_div_pow]
  omega

/-- `add xd, xn, wm, uxtw`. -/
theorem r_addUxtw {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.addSubExt .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .UXTW 0))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + (r k.toNat).toNat % 2 ^ 32))))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_addSubExt]
  simp only [execAddSubExt, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalAddSub, State.writeReg, extendVal]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC, Bool.false_eq_true, if_false]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth, BitVec.toNat_add]
  omega

/-- `mov wd, #(imm << hw)`. -/
theorem r_movz {d : BitVec 5} {imm : BitVec 16} {hw : Nat} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.moveWide .W32 .MOVZ (.gpr d) imm hw))
    (hd : Ok d := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat ((((imm.setWidth 64) <<< hw).setWidth 32).setWidth 64)))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_moveWide]
  simp only [execMoveWide, State.writeReg, wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]

/-- `umull xd, wn, wm`. -/
theorem r_umull {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.dataProc3 .W64 .UMADDL (.gpr d) (.gpr n) (.gpr k) .xzr))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat % 2 ^ 32 * ((r k.toNat).toNat % 2 ^ 32)))))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_dataProc3]
  simp only [execDataProc3, State.readReg32, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    State.writeReg, rd_xzr]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  refine mkS_upd_congr ?_
  simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_mul]

/-- `umaddl xd, wn, wm, xa`. -/
theorem r_umaddl {d n k a : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.dataProc3 .W64 .UMADDL (.gpr d) (.gpr n) (.gpr k) (.gpr a)))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide) (ha : Ok a := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 ((r a.toNat).toNat +
        (r n.toNat).toNat % 2 ^ 32 * ((r k.toNat).toNat % 2 ^ 32)))))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_dataProc3]
  simp only [execDataProc3, State.readReg32, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    rd_gpr _ _ _ _ _ _ _ ha, State.writeReg]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  refine mkS_upd_congr ?_
  simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_mul]

/-! ## Branches -/

theorem r_bCond_t {c : CondCode} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.bCond c off)) (hc : ConditionHolds c ps = true)
    (h : Reach pl Q (mkS s0 (pc + off) sp m ps r)) : Reach pl Q (mkS s0 pc sp m ps r) :=
  reach_step (step_mkS hrun hf (by rw [ex_bCond]; simp [hc])) h

theorem r_bCond_f {c : CondCode} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.bCond c off)) (hc : ConditionHolds c ps = false)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps r)) : Reach pl Q (mkS s0 pc sp m ps r) :=
  reach_step (step_mkS hrun hf (by rw [ex_bCond]; simp [hc])) h

theorem r_b {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.b off))
    (h : Reach pl Q (mkS s0 (pc + off) sp m ps r)) : Reach pl Q (mkS s0 pc sp m ps r) :=
  reach_step (step_mkS hrun hf (by rw [ex_b]; simp)) h

theorem r_cbz_t {n : BitVec 5} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.cbz .W64 false (.gpr n) off)) (hn : Ok n)
    (hz : r n.toNat = 0#64)
    (h : Reach pl Q (mkS s0 (pc + off) sp m ps r)) : Reach pl Q (mkS s0 pc sp m ps r) :=
  reach_step (step_mkS hrun hf (by
    rw [ex_cbz]; simp [State.readReg, rd_gpr _ _ _ _ _ _ _ hn, hz])) h

theorem r_cbz_f {n : BitVec 5} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.cbz .W64 false (.gpr n) off)) (hn : Ok n)
    (hz : r n.toNat ≠ 0#64)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps r)) : Reach pl Q (mkS s0 pc sp m ps r) :=
  reach_step (step_mkS hrun hf (by
    rw [ex_cbz]; simp [State.readReg, rd_gpr _ _ _ _ _ _ _ hn, hz])) h

theorem r_ret (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.ret (.gpr 0x1e#5)))
    (h : Reach pl Q (mkS s0 (s0.readReg64 (.gpr 0x1e#5)) sp m ps r)) :
    Reach pl Q (mkS s0 pc sp m ps r) :=
  reach_step (step_mkS hrun hf (by
    rw [ex_ret, rd_hi _ _ _ _ _ _ _ (by decide)]; simp)) h

end Poly1305Boringssl.Proof
end

section
/-! # Reachability lemmas for the loads and stores of `poly1305_update` -/

namespace Poly1305Boringssl.Proof

open Arm64 Arm64.Obj

variable {pl : Placement} {Q : State → Prop} {s0 : State} {pc sp : BitVec 64} {m : Memory}
  {ps : PState} {r : Nat → BitVec 64}

theorem setWidth_read32 (x : BitVec 32) :
    ((x.setWidth 64).setWidth 32).setWidth 64 = (x.setWidth 64 : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

/-- `ldp wt1, wt2, [xb, #off]`. -/
theorem r_ldp32 {t1 t2 b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.ldp .W32 false (.gpr t1) (.gpr t2) (.Offset (.gpr b) off)))
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hr1 : m.canRead a 4 = true) (hr2 : m.canRead (a + 4#64) 4 = true)
    (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps
      (upd (upd r t1.toNat ((m.read32 a).setWidth 64)) t2.toNat ((m.read32 (a + 4#64)).setWidth 64)))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_ldp]
  simp only [execLdp, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hr1, hr2, Bool.and_self, Bool.not_true,
    MemWidth.bytes, Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ h1,
    wr_gpr _ _ _ _ _ _ _ h2, mkS_advancePC, setWidth_read32]

/-- `ldp wt1, wt2, [sp, #off]`. -/
theorem r_ldp32sp {t1 t2 : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.ldp .W32 false (.gpr t1) (.gpr t2) (.Offset .sp off)))
    (hal : (sp &&& 0b1111#64) = 0#64) (ha : sp + off = a)
    (hr1 : m.canRead a 4 = true) (hr2 : m.canRead (a + 4#64) 4 = true)
    (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps
      (upd (upd r t1.toNat ((m.read32 a).setWidth 64)) t2.toNat ((m.read32 (a + 4#64)).setWidth 64)))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_ldp]
  simp only [execLdp, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned,
    mkS_sp, hal, beq_self_eq_true, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, rd_sp, ha, hr1, hr2, Bool.and_self,
    MemWidth.bytes, Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ h1,
    wr_gpr _ _ _ _ _ _ _ h2, mkS_advancePC, setWidth_read32]

/-- `ldr wt, [xb, #off]`. -/
theorem r_ldr32 {t b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.ldr .W32 .W32 false (.gpr t) (.Offset (.gpr b) off)))
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hr : m.canRead a 4 = true) (ht : Ok t := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps (upd r t.toNat ((m.read32 a).setWidth 64)))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_ldr]
  simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hr,
    MemWidth.bytes, Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ ht,
    mkS_advancePC, setWidth_read32]

/-- `ldrb wt, [xb, xi]`. -/
theorem r_ldrbReg {t b i : BitVec 5} {a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.ldr .W32 .B8 false (.gpr t) (.RegOffset (.gpr b) (.gpr i) .UXTX 0)))
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + (mkS s0 pc sp m ps r).readReg64 (.gpr i) = a)
    (hr : m.canRead a 1 = true) (ht : Ok t := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps (upd r t.toNat ((m.read8 a).setWidth 64)))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_ldr]
  simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, extendVal, BitVec.shiftLeft_zero, ha, hr,
    MemWidth.bytes, Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ ht, mkS_advancePC]
  refine mkS_upd_congr ?_
  simp [BitVec.toNat_setWidth]

/-- `stp wt1, wt2, [xb, #off]`. -/
theorem r_stp32 {t1 t2 b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.stp .W32 (.gpr t1) (.gpr t2) (.Offset (.gpr b) off)))
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hw1 : m.canWrite a 4 = true) (hw2 : m.canWrite (a + 4#64) 4 = true)
    (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp
      ((m.write32 a ((r t1.toNat).setWidth 32)).write32 (a + 4#64) ((r t2.toNat).setWidth 32)) ps r)) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_stp]
  simp only [execStp, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hw1, hw2, Bool.and_self,
    MemWidth.bytes, Memory.writeSized, rd_gpr _ _ _ _ _ _ _ h1, rd_gpr _ _ _ _ _ _ _ h2,
    mkS_setMem, mkS_advancePC]

/-- `str wt, [xb, #off]`. -/
theorem r_str32 {t b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.str .W32 (.gpr t) (.Offset (.gpr b) off)))
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hw : m.canWrite a 4 = true) (ht : Ok t := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp (m.write32 a ((r t.toNat).setWidth 32)) ps r)) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_str]
  simp only [execStr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hw,
    MemWidth.bytes, Memory.writeSized, rd_gpr _ _ _ _ _ _ _ ht, mkS_setMem, mkS_advancePC]

/-- `strb wt, [xb, xi]` (`wt` may be `wzr`). -/
theorem r_strbReg {rt : Reg} {b i : BitVec 5} {a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some (.str .B8 rt (.RegOffset (.gpr b) (.gpr i) .UXTX 0)))
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + (mkS s0 pc sp m ps r).readReg64 (.gpr i) = a)
    (hw : m.canWrite a 1 = true)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp
      (m.write8 a (((mkS s0 pc sp m ps r).readReg64 rt).setWidth 8)) ps r)) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_str]
  simp only [execStr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, extendVal, BitVec.shiftLeft_zero, ha, hw,
    MemWidth.bytes, Memory.writeSized, mkS_setMem, mkS_advancePC]

end Poly1305Boringssl.Proof
end

section
/-! # Addresses of the state words, region membership, word reads over writes -/

namespace Poly1305Boringssl.Proof

open Arm64 Arm64.Obj

theorem add_ofNat_inj (a : BitVec 64) {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    a + BitVec.ofNat 64 x = a + BitVec.ofNat 64 y ↔ x = y := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp [BitVec.toNat_add] at this; omega
  · rintro rfl; rfl

theorem inRegion_off (a : BitVec 64) (c n x : Nat) (h1 : c ≤ x) (h2 : x < c + n) (hx : x < 2 ^ 64) :
    InRegion (a + BitVec.ofNat 64 c) n (a + BitVec.ofNat 64 x) := by
  unfold InRegion
  have : a + BitVec.ofNat 64 x - (a + BitVec.ofNat 64 c) = BitVec.ofNat 64 (x - c) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_add]
    omega
  rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

/-- An accumulator byte is in `W`. -/
theorem W_h (s0 : State) (x : Nat) (h1 : 36 ≤ x) (h2 : x < 56) : W s0 (X0 s0 + BitVec.ofNat 64 x) :=
  Or.inl (by
    have := inRegion_off (X0 s0) 36 20 x h1 (by omega) (by omega)
    simpa using this)

/-- A stack-frame byte is in `W`. -/
theorem W_stk (s0 : State) (x : Nat) (h : x < 16) : W s0 (s0.sp - 16#64 + BitVec.ofNat 64 x) :=
  Or.inr (by
    have := inRegion_off (s0.sp - 16#64) 0 16 x (by omega) (by omega) (by omega)
    simpa using this)

/-- The facts about the first 36 state bytes (`r`, `s`): outside `W`, readable in `s0`. -/
def RSok (s0 : State) : Prop :=
  ∀ k < 36, ¬ W s0 (X0 s0 + BitVec.ofNat 64 k) ∧ (s0.mem.perm (X0 s0 + BitVec.ofNat 64 k)).r = true ∧
    s0.mem.isLazyFree (X0 s0 + BitVec.ofNat 64 k) = false

theorem rs_canRead {s0 : State} {m : Memory} (hm : MemOk s0 m) (hrs : RSok s0) (off : Nat)
    (h : off + 4 ≤ 36) : m.canRead (X0 s0 + BitVec.ofNat 64 off) 4 = true :=
  canRead_notW hm fun k hk => by
    rw [pc_add]; exact hrs (off + k) (by omega)

theorem rs_canRead' {s0 : State} {m : Memory} (hm : MemOk s0 m) (hrs : RSok s0) (off : Nat)
    (h : off + 8 ≤ 36) : m.canRead (X0 s0 + BitVec.ofNat 64 off + 4#64) 4 = true := by
  rw [pc_add]; exact rs_canRead hm hrs (off + 4) (by omega)

theorem h_canWrite {s0 : State} {m : Memory} (hm : MemOk s0 m) (off : Nat)
    (h1 : 36 ≤ off) (h2 : off + 4 ≤ 56) : m.canWrite (X0 s0 + BitVec.ofNat 64 off) 4 = true :=
  canWrite_of hm fun k hk => by rw [pc_add]; exact W_h s0 _ (by omega) (by omega)

theorem h_canWrite' {s0 : State} {m : Memory} (hm : MemOk s0 m) (off : Nat)
    (h1 : 36 ≤ off) (h2 : off + 8 ≤ 56) : m.canWrite (X0 s0 + BitVec.ofNat 64 off + 4#64) 4 = true := by
  rw [pc_add]; exact h_canWrite hm (off + 4) (by omega) (by omega)

theorem h_canRead {s0 : State} {m : Memory} (hm : MemOk s0 m) (off : Nat)
    (h1 : 36 ≤ off) (h2 : off + 4 ≤ 56) : m.canRead (X0 s0 + BitVec.ofNat 64 off) 4 = true :=
  canRead_W hm fun k hk => by rw [pc_add]; exact W_h s0 _ (by omega) (by omega)

theorem h_canRead' {s0 : State} {m : Memory} (hm : MemOk s0 m) (off : Nat)
    (h1 : 36 ≤ off) (h2 : off + 8 ≤ 56) : m.canRead (X0 s0 + BitVec.ofNat 64 off + 4#64) 4 = true := by
  rw [pc_add]; exact h_canRead hm (off + 4) (by omega) (by omega)

/-! ## Words over writes -/

theorem write32_eq (m : Memory) (a : BitVec 64) (v : BitVec 32) :
    m.write32 a v = ((((m.write8 (a + BitVec.ofNat 64 0) (v.extractLsb' 0 8)).write8
      (a + BitVec.ofNat 64 1) (v.extractLsb' 8 8)).write8 (a + BitVec.ofNat 64 2) (v.extractLsb' 16 8)).write8
      (a + BitVec.ofNat 64 3) (v.extractLsb' 24 8)) := rfl

theorem good_write32 {pl : Placement} {s0 : State} {m : Memory} (hg : Good pl s0 m) (off : Nat)
    (h1 : 36 ≤ off) (h2 : off + 4 ≤ 56) (v : BitVec 32) :
    Good pl s0 (m.write32 (X0 s0 + BitVec.ofNat 64 off) v) := by
  rw [write32_eq]
  refine Good.write8 (Good.write8 (Good.write8 (Good.write8 hg ?_ _) ?_ _) ?_ _) ?_ _ <;>
    (rw [pc_add]; exact W_h s0 _ (by omega) (by omega))

theorem read32_eq (m : Memory) (a : BitVec 64) :
    m.read32 a = m.read8 (a + BitVec.ofNat 64 3) ++ m.read8 (a + BitVec.ofNat 64 2) ++
      m.read8 (a + BitVec.ofNat 64 1) ++ m.read8 (a + BitVec.ofNat 64 0) := rfl

theorem concat_bytes32 (v : BitVec 32) :
    v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

theorem ne_off (a : BitVec 64) {x y : Nat} (hx : x + 4 ≤ 2 ^ 32) (hy : y + 4 ≤ 2 ^ 32)
    (hd : x + 4 ≤ y ∨ y + 4 ≤ x ∨ x = y) {i j : Nat} (hi : i < 4) (hj : j < 4)
    (hij : x + 4 ≤ y ∨ y + 4 ≤ x ∨ i ≠ j) :
    (a + BitVec.ofNat 64 (y + i) = a + BitVec.ofNat 64 (x + j)) = False := by
  rw [add_ofNat_inj a (by omega) (by omega)]; simp; omega

/-- The word at `X0 + x` just written. -/
theorem read32_write32_same (m : Memory) (a : BitVec 64) (x : Nat) (v : BitVec 32)
    (hx : x + 4 ≤ 2 ^ 32) : (m.write32 (a + BitVec.ofNat 64 x) v).read32 (a + BitVec.ofNat 64 x) = v := by
  rw [write32_eq, read32_eq]
  simp only [read8_write8, pc_add]
  have hd : x + 4 ≤ x ∨ x + 4 ≤ x ∨ x = x := Or.inr (Or.inr rfl)
  simp only [ne_off a hx hx hd (i := 2) (j := 3) (by decide) (by decide) (by omega), ne_off a hx hx hd (i := 1) (j := 3) (by decide) (by decide) (by omega), ne_off a hx hx hd (i := 1) (j := 2) (by decide) (by decide) (by omega), ne_off a hx hx hd (i := 0) (j := 3) (by decide) (by decide) (by omega), ne_off a hx hx hd (i := 0) (j := 2) (by decide) (by decide) (by omega), ne_off a hx hx hd (i := 0) (j := 1) (by decide) (by decide) (by omega), if_true, if_false]
  exact concat_bytes32 v

/-- A word disjoint from the one written. -/
theorem read32_write32_ne (m : Memory) (a : BitVec 64) (x y : Nat) (v : BitVec 32)
    (hx : x + 4 ≤ 2 ^ 32) (hy : y + 4 ≤ 2 ^ 32) (hd : x + 4 ≤ y ∨ y + 4 ≤ x) :
    (m.write32 (a + BitVec.ofNat 64 x) v).read32 (a + BitVec.ofNat 64 y) = m.read32 (a + BitVec.ofNat 64 y) := by
  rw [write32_eq, read32_eq, read32_eq]
  simp only [read8_write8, pc_add]
  have hd' : x + 4 ≤ y ∨ y + 4 ≤ x ∨ x = y := by omega
  simp only [ne_off a hx hy hd' (i := 0) (j := 0) (by decide) (by decide) (by omega), ne_off a hx hy hd' (i := 0) (j := 1) (by decide) (by decide) (by omega), ne_off a hx hy hd' (i := 0) (j := 2) (by decide) (by decide) (by omega), ne_off a hx hy hd' (i := 0) (j := 3) (by decide) (by decide) (by omega), ne_off a hx hy hd' (i := 1) (j := 0) (by decide) (by decide) (by omega), ne_off a hx hy hd' (i := 1) (j := 1) (by decide) (by decide) (by omega), ne_off a hx hy hd' (i := 1) (j := 2) (by decide) (by decide) (by omega), ne_off a hx hy hd' (i := 1) (j := 3) (by decide) (by decide) (by omega), ne_off a hx hy hd' (i := 2) (j := 0) (by decide) (by decide) (by omega), ne_off a hx hy hd' (i := 2) (j := 1) (by decide) (by decide) (by omega), ne_off a hx hy hd' (i := 2) (j := 2) (by decide) (by decide) (by omega), ne_off a hx hy hd' (i := 2) (j := 3) (by decide) (by decide) (by omega), ne_off a hx hy hd' (i := 3) (j := 0) (by decide) (by decide) (by omega), ne_off a hx hy hd' (i := 3) (j := 1) (by decide) (by decide) (by omega), ne_off a hx hy hd' (i := 3) (j := 2) (by decide) (by decide) (by omega), ne_off a hx hy hd' (i := 3) (j := 3) (by decide) (by decide) (by omega), if_false]

/-- Reading `r`/`s` words: unchanged from `s0`. -/
theorem read32_rs {s0 : State} {m : Memory} (hm : MemOk s0 m) (hrs : RSok s0) (off : Nat)
    (h : off + 4 ≤ 36) : m.read32 (X0 s0 + BitVec.ofNat 64 off) = s0.mem.read32 (X0 s0 + BitVec.ofNat 64 off) := by
  rw [read32_eq, read32_eq]
  simp only [pc_add]
  rw [read8_of_notW hm (hrs _ (by omega)).1, read8_of_notW hm (hrs _ (by omega)).1,
    read8_of_notW hm (hrs _ (by omega)).1, read8_of_notW hm (hrs _ (by omega)).1]

end Poly1305Boringssl.Proof
end

section
/-! # Loads and stores of the state words, with their memory side conditions discharged -/

namespace Poly1305Boringssl.Proof

open Arm64 Arm64.Obj

variable {pl : Placement} {Q : State → Prop} {s0 : State} {pc sp : BitVec 64} {m : Memory}
  {ps : PState} {r : Nat → BitVec 64}

/-- The `r`/`s` word at byte offset `off` of the entry state. -/
abbrev rsW (s0 : State) (off : Nat) : BitVec 64 := (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 off)).setWidth 64

theorem r_ldpRS {t1 t2 : BitVec 5} {off : Nat} (hrun : s0.status = .Running) (hg : Good pl s0 m)
    (hrs : RSok s0)
    (hf : (prog pl).fetchMem m pc =
      some (.ldp .W32 false (.gpr t1) (.gpr t2) (.Offset (.gpr 0#5) (BitVec.ofNat 64 off))))
    (hoff : off + 8 ≤ 36 := by decide) (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps
      (upd (upd r t1.toNat (rsW s0 off)) t2.toNat (rsW s0 (off + 4))))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine r_ldp32 (a := X0 s0 + BitVec.ofNat 64 off) hrun hf rfl (rs_canRead hg.2.2 hrs off (by omega))
    (rs_canRead' hg.2.2 hrs off hoff) h1 h2 (h := ?_)
  rw [read32_rs hg.2.2 hrs off (by omega), pc_add, read32_rs hg.2.2 hrs (off + 4) (by omega)]
  exact h

theorem r_ldrRS {t : BitVec 5} {off : Nat} (hrun : s0.status = .Running) (hg : Good pl s0 m)
    (hrs : RSok s0)
    (hf : (prog pl).fetchMem m pc =
      some (.ldr .W32 .W32 false (.gpr t) (.Offset (.gpr 0#5) (BitVec.ofNat 64 off))))
    (hoff : off + 4 ≤ 36 := by decide) (ht : Ok t := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps (upd r t.toNat (rsW s0 off)))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine r_ldr32 (a := X0 s0 + BitVec.ofNat 64 off) hrun hf rfl (rs_canRead hg.2.2 hrs off hoff)
    ht (h := ?_)
  rw [read32_rs hg.2.2 hrs off hoff]
  exact h

/-- The accumulator word at byte offset `off` of the state in memory `m`. -/
abbrev hW (s0 : State) (m : Memory) (off : Nat) : BitVec 64 :=
  (m.read32 (X0 s0 + BitVec.ofNat 64 off)).setWidth 64

theorem r_ldpH {t1 t2 : BitVec 5} {off : Nat} (hrun : s0.status = .Running) (hg : Good pl s0 m)
    (hf : (prog pl).fetchMem m pc =
      some (.ldp .W32 false (.gpr t1) (.gpr t2) (.Offset (.gpr 0#5) (BitVec.ofNat 64 off))))
    (ho1 : 36 ≤ off := by decide) (ho2 : off + 8 ≤ 56 := by decide)
    (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps
      (upd (upd r t1.toNat (hW s0 m off)) t2.toNat (hW s0 m (off + 4))))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine r_ldp32 (a := X0 s0 + BitVec.ofNat 64 off) hrun hf rfl (h_canRead hg.2.2 off ho1 (by omega))
    (h_canRead' hg.2.2 off ho1 ho2) h1 h2 (h := ?_)
  rw [pc_add]
  exact h

theorem r_ldrH {t : BitVec 5} {off : Nat} (hrun : s0.status = .Running) (hg : Good pl s0 m)
    (hf : (prog pl).fetchMem m pc =
      some (.ldr .W32 .W32 false (.gpr t) (.Offset (.gpr 0#5) (BitVec.ofNat 64 off))))
    (ho1 : 36 ≤ off := by decide) (ho2 : off + 4 ≤ 56 := by decide) (ht : Ok t := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps (upd r t.toNat (hW s0 m off)))) :
    Reach pl Q (mkS s0 pc sp m ps r) :=
  r_ldr32 (a := X0 s0 + BitVec.ofNat 64 off) hrun hf rfl (h_canRead hg.2.2 off ho1 ho2) ht (h := h)

theorem r_stpH {t1 t2 : BitVec 5} {off : Nat} (hrun : s0.status = .Running) (hg : Good pl s0 m)
    (hf : (prog pl).fetchMem m pc =
      some (.stp .W32 (.gpr t1) (.gpr t2) (.Offset (.gpr 0#5) (BitVec.ofNat 64 off))))
    (ho1 : 36 ≤ off := by decide) (ho2 : off + 8 ≤ 56 := by decide)
    (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide)
    (h : Good pl s0 ((m.write32 (X0 s0 + BitVec.ofNat 64 off) ((r t1.toNat).setWidth 32)).write32
          (X0 s0 + BitVec.ofNat 64 (off + 4)) ((r t2.toNat).setWidth 32)) →
      Reach pl Q (mkS s0 (pc + 4#64) sp
        ((m.write32 (X0 s0 + BitVec.ofNat 64 off) ((r t1.toNat).setWidth 32)).write32
          (X0 s0 + BitVec.ofNat 64 (off + 4)) ((r t2.toNat).setWidth 32)) ps r)) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  refine r_stp32 (a := X0 s0 + BitVec.ofNat 64 off) hrun hf rfl (h_canWrite hg.2.2 off ho1 (by omega))
    (h_canWrite' hg.2.2 off ho1 ho2) h1 h2 (h := ?_)
  rw [pc_add]
  exact h (good_write32 (good_write32 hg off ho1 (by omega) _) (off + 4) (by omega) (by omega) _)

theorem r_strH {t : BitVec 5} {off : Nat} (hrun : s0.status = .Running) (hg : Good pl s0 m)
    (hf : (prog pl).fetchMem m pc =
      some (.str .W32 (.gpr t) (.Offset (.gpr 0#5) (BitVec.ofNat 64 off))))
    (ho1 : 36 ≤ off := by decide) (ho2 : off + 4 ≤ 56 := by decide) (ht : Ok t := by decide)
    (h : Good pl s0 (m.write32 (X0 s0 + BitVec.ofNat 64 off) ((r t.toNat).setWidth 32)) →
      Reach pl Q (mkS s0 (pc + 4#64) sp (m.write32 (X0 s0 + BitVec.ofNat 64 off) ((r t.toNat).setWidth 32)) ps r)) :
    Reach pl Q (mkS s0 pc sp m ps r) :=
  r_str32 (a := X0 s0 + BitVec.ofNat 64 off) hrun hf rfl (h_canWrite hg.2.2 off ho1 ho2) ht
    (h := h (good_write32 hg off ho1 ho2 _))

/-- Normalizing `pc` after a step. -/
theorem nx {pl : Placement} {Q : State → Prop} {s0 : State} {sp : BitVec 64} {m : Memory}
    {ps : PState} {r : Nat → BitVec 64} (b : BitVec 64) (x y : Nat) (hxy : x + 4 = y := by decide)
    (h : Reach pl Q (mkS s0 (b + BitVec.ofNat 64 y) sp m ps r)) :
    Reach pl Q (mkS s0 (b + BitVec.ofNat 64 x + 4#64) sp m ps r) := by
  rw [pc_add, hxy]; exact h

/-- `toNat` of the `r`/`s` word at byte offset `off`. -/
abbrev Rw (s0 : State) (off : Nat) : Nat := (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 off)).toNat

theorem rsW_toNat32 (s0 : State) (off : Nat) : (rsW s0 off).toNat % 2 ^ 32 = Rw s0 off := by
  have := (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 off)).isLt
  simp [rsW, BitVec.toNat_setWidth]; omega

theorem toNat_eq_of {v : BitVec 64} {E : Nat} (h : v = BitVec.ofNat 64 E) : v.toNat = E % 2 ^ 64 := by
  subst h; simp

theorem setWidth32_id {v : BitVec 64} (h : v.toNat < 2 ^ 32) : (v.setWidth 32).setWidth 64 = v := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]; omega

theorem w32_mod (x : BitVec 32) : x.toNat % 18446744073709551616 % 4294967296 = x.toNat := by
  have := x.isLt; omega

/-- Name the value just written to a register (keeps terms linear in size). -/
theorem reach_gen {pl : Placement} {Q : State → Prop} {s0 : State} {pc sp : BitVec 64} {m : Memory}
    {ps : PState} {r : Nat → BitVec 64} {k : Nat} {v : BitVec 64}
    (h : ∀ w, w = v → Reach pl Q (mkS s0 pc sp m ps (upd r k w))) :
    Reach pl Q (mkS s0 pc sp m ps (upd r k v)) := h v rfl

end Poly1305Boringssl.Proof
end

section
/-! # The arithmetic core, independent of the machine

`a0..a4`: the limbs of `h + block` (26-bit radix, unreduced); `r0..r4`, `s_i = 5 r_i`: the key.
The code computes the five column sums `dd_i`, carries them (`tt_i`), and folds the top carry
back times 5 (`oh_i` are the new limbs). -/

namespace Poly1305Boringssl.Proof

section
variable (a0 a1 a2 a3 a4 r0 r1 r2 r3 r4 s1 s2 s3 s4 : Nat)

def dd0 : Nat := r0 * a0 + s4 * a1 + s3 * a2 + s2 * a3 + s1 * a4
def dd1 : Nat := r0 * a1 + s4 * a2 + s3 * a3 + s2 * a4 + r1 * a0
def dd2 : Nat := r0 * a2 + s4 * a3 + s3 * a4 + r1 * a1 + r2 * a0
def dd3 : Nat := r0 * a3 + s4 * a4 + r1 * a2 + r2 * a1 + r3 * a0
def dd4 : Nat := r0 * a4 + r1 * a3 + r2 * a2 + r3 * a1 + r4 * a0

def tt1 : Nat := dd1 a0 a1 a2 a3 a4 r0 r1 s2 s3 s4 + dd0 a0 a1 a2 a3 a4 r0 s1 s2 s3 s4 / 2 ^ 26
def tt2 : Nat := dd2 a0 a1 a2 a3 a4 r0 r1 r2 s3 s4 + tt1 a0 a1 a2 a3 a4 r0 r1 s1 s2 s3 s4 / 2 ^ 26
def tt3 : Nat := dd3 a0 a1 a2 a3 a4 r0 r1 r2 r3 s4 + tt2 a0 a1 a2 a3 a4 r0 r1 r2 s1 s2 s3 s4 / 2 ^ 26
def tt4 : Nat := dd4 a0 a1 a2 a3 a4 r0 r1 r2 r3 r4 + tt3 a0 a1 a2 a3 a4 r0 r1 r2 r3 s1 s2 s3 s4 / 2 ^ 26

/-- The new limb 0: `5 * carry + (dd0 mod 2^26)`. -/
def oh0 : Nat := 5 * (tt4 a0 a1 a2 a3 a4 r0 r1 r2 r3 r4 s1 s2 s3 s4 / 2 ^ 26) +
  dd0 a0 a1 a2 a3 a4 r0 s1 s2 s3 s4 % 2 ^ 26

end

/-- `A * R ≡ limbVal (new limbs) (mod 2^130 - 5)` when `s_i = 5 r_i`. -/
theorem mul_mod (a0 a1 a2 a3 a4 r0 r1 r2 r3 r4 : Nat) :
    (oh0 a0 a1 a2 a3 a4 r0 r1 r2 r3 r4 (5 * r1) (5 * r2) (5 * r3) (5 * r4) +
      2 ^ 26 * (tt1 a0 a1 a2 a3 a4 r0 r1 (5 * r1) (5 * r2) (5 * r3) (5 * r4) % 2 ^ 26) +
      2 ^ 52 * (tt2 a0 a1 a2 a3 a4 r0 r1 r2 (5 * r1) (5 * r2) (5 * r3) (5 * r4) % 2 ^ 26) +
      2 ^ 78 * (tt3 a0 a1 a2 a3 a4 r0 r1 r2 r3 (5 * r1) (5 * r2) (5 * r3) (5 * r4) % 2 ^ 26) +
      2 ^ 104 * (tt4 a0 a1 a2 a3 a4 r0 r1 r2 r3 r4 (5 * r1) (5 * r2) (5 * r3) (5 * r4) % 2 ^ 26)) %
        p1305 =
    ((a0 + 2 ^ 26 * a1 + 2 ^ 52 * a2 + 2 ^ 78 * a3 + 2 ^ 104 * a4) *
      (r0 + 2 ^ 26 * r1 + 2 ^ 52 * r2 + 2 ^ 78 * r3 + 2 ^ 104 * r4)) % p1305 := by
  -- the carry chain: new limbs + 2^130 c = D + 5 c
  generalize hD0 : dd0 a0 a1 a2 a3 a4 r0 (5 * r1) (5 * r2) (5 * r3) (5 * r4) = D0
  generalize hD1 : dd1 a0 a1 a2 a3 a4 r0 r1 (5 * r2) (5 * r3) (5 * r4) = D1
  generalize hD2 : dd2 a0 a1 a2 a3 a4 r0 r1 r2 (5 * r3) (5 * r4) = D2
  generalize hD3 : dd3 a0 a1 a2 a3 a4 r0 r1 r2 r3 (5 * r4) = D3
  generalize hD4 : dd4 a0 a1 a2 a3 a4 r0 r1 r2 r3 r4 = D4
  have hc : oh0 a0 a1 a2 a3 a4 r0 r1 r2 r3 r4 (5 * r1) (5 * r2) (5 * r3) (5 * r4) +
      2 ^ 26 * (tt1 a0 a1 a2 a3 a4 r0 r1 (5 * r1) (5 * r2) (5 * r3) (5 * r4) % 2 ^ 26) +
      2 ^ 52 * (tt2 a0 a1 a2 a3 a4 r0 r1 r2 (5 * r1) (5 * r2) (5 * r3) (5 * r4) % 2 ^ 26) +
      2 ^ 78 * (tt3 a0 a1 a2 a3 a4 r0 r1 r2 r3 (5 * r1) (5 * r2) (5 * r3) (5 * r4) % 2 ^ 26) +
      2 ^ 104 * (tt4 a0 a1 a2 a3 a4 r0 r1 r2 r3 r4 (5 * r1) (5 * r2) (5 * r3) (5 * r4) % 2 ^ 26) +
      p1305 * (tt4 a0 a1 a2 a3 a4 r0 r1 r2 r3 r4 (5 * r1) (5 * r2) (5 * r3) (5 * r4) / 2 ^ 26) =
      D0 + 2 ^ 26 * D1 + 2 ^ 52 * D2 + 2 ^ 78 * D3 + 2 ^ 104 * D4 := by
    simp only [oh0, tt4, tt3, tt2, tt1, hD0, hD1, hD2, hD3, hD4, p1305]
    omega
  -- the product: A * R = D + p * E
  have hp : (a0 + 2 ^ 26 * a1 + 2 ^ 52 * a2 + 2 ^ 78 * a3 + 2 ^ 104 * a4) *
      (r0 + 2 ^ 26 * r1 + 2 ^ 52 * r2 + 2 ^ 78 * r3 + 2 ^ 104 * r4) =
      D0 + 2 ^ 26 * D1 + 2 ^ 52 * D2 + 2 ^ 78 * D3 + 2 ^ 104 * D4 +
      p1305 * (a1 * r4 + a2 * r3 + a3 * r2 + a4 * r1 + 2 ^ 26 * (a2 * r4 + a3 * r3 + a4 * r2) +
        2 ^ 52 * (a3 * r4 + a4 * r3) + 2 ^ 78 * (a4 * r4)) := by
    subst hD0 hD1 hD2 hD3 hD4
    simp only [dd0, dd1, dd2, dd3, dd4, p1305]
    have : (2 : Nat) ^ 130 = (2 ^ 130 - 5) + 5 := by norm_num
    rw [show (2 : Nat) ^ 130 - 5 = 1361129467683753853853498429727072845819 by norm_num]
    ring
  have key : ∀ L c E : Nat, (L + p1305 * c + p1305 * E) % p1305 = L % p1305 := by
    intro L c E; rw [Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left]
  rw [hp, ← hc, key]

/-- The bounds that keep every machine operation exact and preserve `StateOk`. -/
theorem mul_bounds (a0 a1 a2 a3 a4 r0 r1 r2 r3 r4 : Nat)
    (ha0 : a0 < 2 ^ 31 + 2 ^ 29 + 2 ^ 27 + 2 ^ 26) (ha1 : a1 < 2 ^ 27) (ha2 : a2 < 2 ^ 27)
    (ha3 : a3 < 2 ^ 27) (ha4 : a4 < 2 ^ 26 + 2 ^ 25)
    (hr0 : r0 ≤ 0x3ffffff) (hr1 : r1 ≤ 0x3ffff03) (hr2 : r2 ≤ 0x3ffc0ff) (hr3 : r3 ≤ 0x3f03fff)
    (hr4 : r4 ≤ 0x00fffff) :
    dd0 a0 a1 a2 a3 a4 r0 (5 * r1) (5 * r2) (5 * r3) (5 * r4) < 2 ^ 64 ∧
    tt1 a0 a1 a2 a3 a4 r0 r1 (5 * r1) (5 * r2) (5 * r3) (5 * r4) < 2 ^ 58 ∧
    tt2 a0 a1 a2 a3 a4 r0 r1 r2 (5 * r1) (5 * r2) (5 * r3) (5 * r4) < 2 ^ 58 ∧
    tt3 a0 a1 a2 a3 a4 r0 r1 r2 r3 (5 * r1) (5 * r2) (5 * r3) (5 * r4) < 2 ^ 58 ∧
    tt4 a0 a1 a2 a3 a4 r0 r1 r2 r3 r4 (5 * r1) (5 * r2) (5 * r3) (5 * r4) < 2 ^ 58 ∧
    oh0 a0 a1 a2 a3 a4 r0 r1 r2 r3 r4 (5 * r1) (5 * r2) (5 * r3) (5 * r4) < 2 ^ 31 + 2 ^ 29 + 2 ^ 27 := by
  have m := fun {x y X Y : Nat} (hx : x ≤ X) (hy : y ≤ Y) => Nat.mul_le_mul hx hy
  have A0 : a0 ≤ 2818572288 + 67108863 := by omega
  have A1 : a1 ≤ 134217727 := by omega
  have A2 : a2 ≤ 134217727 := by omega
  have A3 : a3 ≤ 134217727 := by omega
  have A4 : a4 ≤ 100663295 := by omega
  have S1 : 5 * r1 ≤ 5 * 0x3ffff03 := by omega
  have S2 : 5 * r2 ≤ 5 * 0x3ffc0ff := by omega
  have S3 : 5 * r3 ≤ 5 * 0x3f03fff := by omega
  have S4 : 5 * r4 ≤ 5 * 0x00fffff := by omega
  have := m hr0 A0; have := m hr0 A1; have := m hr0 A2; have := m hr0 A3; have := m hr0 A4
  have := m hr1 A0; have := m hr1 A1; have := m hr1 A2; have := m hr1 A3
  have := m hr2 A0; have := m hr2 A1; have := m hr2 A2
  have := m hr3 A0; have := m hr3 A1; have := m hr4 A0
  have := m S4 A1; have := m S4 A2; have := m S4 A3; have := m S4 A4
  have := m S3 A2; have := m S3 A3; have := m S3 A4
  have := m S2 A3; have := m S2 A4; have := m S1 A4
  simp only [oh0, tt4, tt3, tt2, tt1, dd0, dd1, dd2, dd3, dd4]
  omega

end Poly1305Boringssl.Proof
end

section
/-! # The multiply-and-reduce segment (block offsets 0x6c..0x12c)

Entered with the unreduced limbs `a_i` of `h + block` in `x8..x12`; leaves the new limbs in
`x8..x12` and stored in the state, with the flags of `cmp x2, #15`. Both the full-block path and
the partial-block path jump here. -/

namespace Poly1305Boringssl.Proof

open Arm64 Arm64.Obj

/-- The key words as `CRYPTO_poly1305_init` leaves them. -/
def KeyOk (s0 : State) : Prop :=
  Rw s0 0 ≤ 0x3ffffff ∧ Rw s0 4 ≤ 0x3ffff03 ∧ Rw s0 8 ≤ 0x3ffc0ff ∧ Rw s0 12 ≤ 0x3f03fff ∧
  Rw s0 16 ≤ 0x00fffff ∧ Rw s0 20 = 5 * Rw s0 4 ∧ Rw s0 24 = 5 * Rw s0 8 ∧
  Rw s0 28 = 5 * Rw s0 12 ∧ Rw s0 32 = 5 * Rw s0 16

/-- What the segment leaves: new limbs in `x8..x12` and in the state words, `x1`, `x2` kept. -/
def MulPost (s0 : State) (X1 X2 : BitVec 64) (m' : Memory) (r' : Nat → BitVec 64)
    (a0 a1 a2 a3 a4 : Nat) : Prop :=
  r' 1 = X1 ∧ r' 2 = X2 ∧
  (r' 8).toNat = oh0 a0 a1 a2 a3 a4 (Rw s0 0) (Rw s0 4) (Rw s0 8) (Rw s0 12) (Rw s0 16)
    (Rw s0 20) (Rw s0 24) (Rw s0 28) (Rw s0 32) ∧
  (r' 9).toNat = tt1 a0 a1 a2 a3 a4 (Rw s0 0) (Rw s0 4)
    (Rw s0 20) (Rw s0 24) (Rw s0 28) (Rw s0 32) % 2 ^ 26 ∧
  (r' 10).toNat = tt2 a0 a1 a2 a3 a4 (Rw s0 0) (Rw s0 4) (Rw s0 8)
    (Rw s0 20) (Rw s0 24) (Rw s0 28) (Rw s0 32) % 2 ^ 26 ∧
  (r' 11).toNat = tt3 a0 a1 a2 a3 a4 (Rw s0 0) (Rw s0 4) (Rw s0 8) (Rw s0 12)
    (Rw s0 20) (Rw s0 24) (Rw s0 28) (Rw s0 32) % 2 ^ 26 ∧
  (r' 12).toNat = tt4 a0 a1 a2 a3 a4 (Rw s0 0) (Rw s0 4) (Rw s0 8) (Rw s0 12) (Rw s0 16)
    (Rw s0 20) (Rw s0 24) (Rw s0 28) (Rw s0 32) % 2 ^ 26 ∧
  (m'.read32 (X0 s0 + BitVec.ofNat 64 36)).setWidth 64 = r' 8 ∧
  (m'.read32 (X0 s0 + BitVec.ofNat 64 40)).setWidth 64 = r' 9 ∧
  (m'.read32 (X0 s0 + BitVec.ofNat 64 44)).setWidth 64 = r' 10 ∧
  (m'.read32 (X0 s0 + BitVec.ofNat 64 48)).setWidth 64 = r' 11 ∧
  (m'.read32 (X0 s0 + BitVec.ofNat 64 52)).setWidth 64 = r' 12

theorem reach_ps {pl : Placement} {Q : State → Prop} {s0 : State} {pc sp : BitVec 64} {m : Memory}
    {ps ps' : PState} {r : Nat → BitVec 64} (e : ps = ps') (h : Reach pl Q (mkS s0 pc sp m ps' r)) :
    Reach pl Q (mkS s0 pc sp m ps r) := e ▸ h

set_option maxHeartbeats 4000000 in
theorem mulSeg {pl : Placement} {Q : State → Prop} {s0 : State} {sp : BitVec 64} {m : Memory}
    {ps : PState} {r : Nat → BitVec 64} (hrun : s0.status = .Running) (hg : Good pl s0 m)
    (hrs : RSok s0) (hkey : KeyOk s0) {X1 X2 : BitVec 64} (hx1 : r 1 = X1) (hx2 : r 2 = X2)
    {a0 a1 a2 a3 a4 : Nat}
    (h8 : (r 8).toNat = a0) (h9 : (r 9).toNat = a1) (h10 : (r 10).toNat = a2)
    (h11 : (r 11).toNat = a3) (h12 : (r 12).toNat = a4)
    (ha0 : a0 < 2 ^ 31 + 2 ^ 29 + 2 ^ 27 + 2 ^ 26) (ha1 : a1 < 2 ^ 27) (ha2 : a2 < 2 ^ 27)
    (ha3 : a3 < 2 ^ 27) (ha4 : a4 < 2 ^ 26 + 2 ^ 25)
    (k : ∀ m' r', Good pl s0 m' → MulPost s0 X1 X2 m' r' a0 a1 a2 a3 a4 →
      Reach pl Q (mkS s0 (pl.base + 668#64) sp m' (subFlags X2 15#64) r')) :
    Reach pl Q (mkS s0 (pl.base + 472#64) sp m ps r) := by
  refine r_ldpRS hrun hg hrs (f_6c hg) (h := ?_)
  refine nx pl.base 472 476 (h := ?_)
  refine r_ldpRS hrun hg hrs (f_70 hg) (h := ?_)
  refine nx pl.base 476 480 (h := ?_)
  refine r_ldpRS hrun hg hrs (f_74 hg) (h := ?_)
  refine nx pl.base 480 484 (h := ?_)
  refine r_umull hrun (f_78 hg) (h := ?_)
  refine nx pl.base 484 488 (h := ?_)
  refine reach_gen fun v78 e78 => ?_
  refine r_cmpImm hrun (f_7c hg) (h := ?_)
  refine nx pl.base 488 492 (h := ?_)
  refine r_umull hrun (f_80 hg) (h := ?_)
  refine nx pl.base 492 496 (h := ?_)
  refine reach_gen fun v80 e80 => ?_
  refine r_umaddl hrun (f_84 hg) (h := ?_)
  refine nx pl.base 496 500 (h := ?_)
  refine reach_gen fun v84 e84 => ?_
  refine r_umaddl hrun (f_88 hg) (h := ?_)
  refine nx pl.base 500 504 (h := ?_)
  refine reach_gen fun v88 e88 => ?_
  refine r_umaddl hrun (f_8c hg) (h := ?_)
  refine nx pl.base 504 508 (h := ?_)
  refine reach_gen fun v8c e8c => ?_
  refine r_umaddl hrun (f_90 hg) (h := ?_)
  refine nx pl.base 508 512 (h := ?_)
  refine reach_gen fun v90 e90 => ?_
  refine r_umaddl hrun (f_94 hg) (h := ?_)
  refine nx pl.base 512 516 (h := ?_)
  refine reach_gen fun v94 e94 => ?_
  refine r_umaddl hrun (f_98 hg) (h := ?_)
  refine nx pl.base 516 520 (h := ?_)
  refine reach_gen fun v98 e98 => ?_
  refine r_ldrRS hrun hg hrs (f_9c hg) (h := ?_)
  refine nx pl.base 520 524 (h := ?_)
  refine r_umull hrun (f_a0 hg) (h := ?_)
  refine nx pl.base 524 528 (h := ?_)
  refine reach_gen fun va0 ea0 => ?_
  refine r_umaddl hrun (f_a4 hg) (h := ?_)
  refine nx pl.base 528 532 (h := ?_)
  refine reach_gen fun va4 ea4 => ?_
  refine r_umaddl hrun (f_a8 hg) (h := ?_)
  refine nx pl.base 532 536 (h := ?_)
  refine reach_gen fun va8 ea8 => ?_
  refine r_umaddl hrun (f_ac hg) (h := ?_)
  refine nx pl.base 536 540 (h := ?_)
  refine reach_gen fun vac eac => ?_
  refine r_umaddl hrun (f_b0 hg) (h := ?_)
  refine nx pl.base 540 544 (h := ?_)
  refine reach_gen fun vb0 eb0 => ?_
  refine r_add64lsr26 hrun (f_b4 hg) (h := ?_)
  refine nx pl.base 544 548 (h := ?_)
  refine reach_gen fun vb4 eb4 => ?_
  refine r_umaddl hrun (f_b8 hg) (h := ?_)
  refine nx pl.base 548 552 (h := ?_)
  refine reach_gen fun vb8 eb8 => ?_
  refine r_andMask hrun (f_bc hg) (h := ?_)
  refine nx pl.base 552 556 (h := ?_)
  refine reach_gen fun vbc ebc => ?_
  refine r_umull hrun (f_c0 hg) (h := ?_)
  refine nx pl.base 556 560 (h := ?_)
  refine reach_gen fun vc0 ec0 => ?_
  refine r_umaddl hrun (f_c4 hg) (h := ?_)
  refine nx pl.base 560 564 (h := ?_)
  refine reach_gen fun vc4 ec4 => ?_
  refine r_lsr26 hrun (f_c8 hg) (h := ?_)
  refine nx pl.base 564 568 (h := ?_)
  refine reach_gen fun vc8 ec8 => ?_
  refine r_umull hrun (f_cc hg) (h := ?_)
  refine nx pl.base 568 572 (h := ?_)
  refine reach_gen fun vcc ecc => ?_
  refine r_ldpRS hrun hg hrs (f_d0 hg) (h := ?_)
  refine nx pl.base 572 576 (h := ?_)
  refine r_umaddl hrun (f_d4 hg) (h := ?_)
  refine nx pl.base 576 580 (h := ?_)
  refine reach_gen fun vd4 ed4 => ?_
  refine r_addUxtw hrun (f_d8 hg) (h := ?_)
  refine nx pl.base 580 584 (h := ?_)
  refine reach_gen fun vd8 ed8 => ?_
  refine r_umaddl hrun (f_dc hg) (h := ?_)
  refine nx pl.base 584 588 (h := ?_)
  refine reach_gen fun vdc edc => ?_
  refine r_umaddl hrun (f_e0 hg) (h := ?_)
  refine nx pl.base 588 592 (h := ?_)
  refine reach_gen fun ve0 ee0 => ?_
  refine r_lsr26 hrun (f_e4 hg) (h := ?_)
  refine nx pl.base 592 596 (h := ?_)
  refine reach_gen fun ve4 ee4 => ?_
  refine r_umaddl hrun (f_e8 hg) (h := ?_)
  refine nx pl.base 596 600 (h := ?_)
  refine reach_gen fun ve8 ee8 => ?_
  refine r_umaddl hrun (f_ec hg) (h := ?_)
  refine nx pl.base 600 604 (h := ?_)
  refine reach_gen fun vec eec => ?_
  refine r_umaddl hrun (f_f0 hg) (h := ?_)
  refine nx pl.base 604 608 (h := ?_)
  refine reach_gen fun vf0 ef0 => ?_
  refine r_addUxtw hrun (f_f4 hg) (h := ?_)
  refine nx pl.base 608 612 (h := ?_)
  refine reach_gen fun vf4 ef4 => ?_
  refine r_umaddl hrun (f_f8 hg) (h := ?_)
  refine nx pl.base 612 616 (h := ?_)
  refine reach_gen fun vf8 ef8 => ?_
  refine r_andMask hrun (f_fc hg) (h := ?_)
  refine nx pl.base 616 620 (h := ?_)
  refine reach_gen fun vfc efc => ?_
  refine r_umaddl hrun (f_100 hg) (h := ?_)
  refine nx pl.base 620 624 (h := ?_)
  refine reach_gen fun v100 e100 => ?_
  refine r_lsr26 hrun (f_104 hg) (h := ?_)
  refine nx pl.base 624 628 (h := ?_)
  refine reach_gen fun v104 e104 => ?_
  refine r_andMask hrun (f_108 hg) (h := ?_)
  refine nx pl.base 628 632 (h := ?_)
  refine reach_gen fun v108 e108 => ?_
  refine r_stpH hrun hg (f_10c hg) (h := fun hg1 => ?_)
  refine nx pl.base 632 636 (h := ?_)
  refine r_addUxtw hrun (f_110 hg1) (h := ?_)
  refine nx pl.base 636 640 (h := ?_)
  refine reach_gen fun v110 e110 => ?_
  refine r_lsr26 hrun (f_114 hg1) (h := ?_)
  refine nx pl.base 640 644 (h := ?_)
  refine reach_gen fun v114 e114 => ?_
  refine r_andMask hrun (f_118 hg1) (h := ?_)
  refine nx pl.base 644 648 (h := ?_)
  refine reach_gen fun v118 e118 => ?_
  refine r_strH hrun hg1 (f_11c hg1) (h := fun hg2 => ?_)
  refine nx pl.base 648 652 (h := ?_)
  refine r_add32 hrun (f_120 hg2) (h := ?_)
  refine nx pl.base 652 656 (h := ?_)
  refine reach_gen fun v120 e120 => ?_
  refine r_andMask hrun (f_124 hg2) (h := ?_)
  refine nx pl.base 656 660 (h := ?_)
  refine reach_gen fun v124 e124 => ?_
  refine r_add32 hrun (f_128 hg2) (h := ?_)
  refine nx pl.base 660 664 (h := ?_)
  refine reach_gen fun v128 e128 => ?_
  refine r_stpH hrun hg2 (f_12c hg2) (h := fun hg3 => ?_)
  refine nx pl.base 664 668 (h := ?_)
  obtain ⟨k0, k1, k2, k3, k4, s1, s2, s3, s4⟩ := hkey
  have i8 : (r 8).toNat % 4294967296 = a0 := by omega
  have i9 : (r 9).toNat % 4294967296 = a1 := by omega
  have i10 : (r 10).toNat % 4294967296 = a2 := by omega
  have i11 : (r 11).toNat % 4294967296 = a3 := by omega
  have i12 : (r 12).toNat % 4294967296 = a4 := by omega
  simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceEqDiff,
    reduceIte, rsW_toNat32, w32_mod, i8, i9, i10, i11, i12, shift32, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at e78 e80 e84 e88 e8c e90 e94 e98 ea0 ea4 ea8 eac eb0 eb4 eb8 ebc ec0 ec4 ec8 ecc ed4 ed8 edc ee0 ee4 ee8 eec ef0 ef4 ef8 efc e100 e104 e108 e110 e114 e118 e120 e124 e128
  have t78 := toNat_eq_of e78
  have t80 := toNat_eq_of e80
  have t84 := toNat_eq_of e84
  have t88 := toNat_eq_of e88
  have t8c := toNat_eq_of e8c
  have t90 := toNat_eq_of e90
  have t94 := toNat_eq_of e94
  have t98 := toNat_eq_of e98
  have ta0 := toNat_eq_of ea0
  have ta4 := toNat_eq_of ea4
  have ta8 := toNat_eq_of ea8
  have tac := toNat_eq_of eac
  have tb0 := toNat_eq_of eb0
  have tb4 := toNat_eq_of eb4
  have tb8 := toNat_eq_of eb8
  have tbc := toNat_eq_of ebc
  have tc0 := toNat_eq_of ec0
  have tc4 := toNat_eq_of ec4
  have tc8 := toNat_eq_of ec8
  have tcc := toNat_eq_of ecc
  have td4 := toNat_eq_of ed4
  have td8 := toNat_eq_of ed8
  have tdc := toNat_eq_of edc
  have te0 := toNat_eq_of ee0
  have te4 := toNat_eq_of ee4
  have te8 := toNat_eq_of ee8
  have tec := toNat_eq_of eec
  have tf0 := toNat_eq_of ef0
  have tf4 := toNat_eq_of ef4
  have tf8 := toNat_eq_of ef8
  have tfc := toNat_eq_of efc
  have t100 := toNat_eq_of e100
  have t104 := toNat_eq_of e104
  have t108 := toNat_eq_of e108
  have t110 := toNat_eq_of e110
  have t114 := toNat_eq_of e114
  have t118 := toNat_eq_of e118
  have t120 := toNat_eq_of e120
  have t124 := toNat_eq_of e124
  have t128 := toNat_eq_of e128
  simp only [Rw] at k0 k1 k2 k3 k4 s1 s2 s3 s4
  have A0 : a0 ≤ 2818572288 + 67108863 := by omega
  have A1 : a1 ≤ 134217727 := by omega
  have A2 : a2 ≤ 134217727 := by omega
  have A3 : a3 ≤ 134217727 := by omega
  have A4 : a4 ≤ 100663295 := by omega
  have S1 : (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 20)).toNat ≤ 5 * 0x3ffff03 := by omega
  have S2 : (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 24)).toNat ≤ 5 * 0x3ffc0ff := by omega
  have S3 : (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 28)).toNat ≤ 5 * 0x3f03fff := by omega
  have S4 : (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 32)).toNat ≤ 5 * 0x00fffff := by omega
  have := Nat.mul_le_mul k0 A0; have := Nat.mul_le_mul k0 A1; have := Nat.mul_le_mul k0 A2
  have := Nat.mul_le_mul k0 A3; have := Nat.mul_le_mul k0 A4
  have := Nat.mul_le_mul k1 A0; have := Nat.mul_le_mul k1 A1; have := Nat.mul_le_mul k1 A2
  have := Nat.mul_le_mul k1 A3
  have := Nat.mul_le_mul k2 A0; have := Nat.mul_le_mul k2 A1; have := Nat.mul_le_mul k2 A2
  have := Nat.mul_le_mul k3 A0; have := Nat.mul_le_mul k3 A1; have := Nat.mul_le_mul k4 A0
  have := Nat.mul_le_mul S4 A1; have := Nat.mul_le_mul S4 A2; have := Nat.mul_le_mul S4 A3
  have := Nat.mul_le_mul S4 A4
  have := Nat.mul_le_mul S3 A2; have := Nat.mul_le_mul S3 A3; have := Nat.mul_le_mul S3 A4
  have := Nat.mul_le_mul S2 A3; have := Nat.mul_le_mul S2 A4; have := Nat.mul_le_mul S1 A4
  have q78 : v78.toNat = (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 0)).toNat * a0 := by rw [t78]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have q80 : v80.toNat = (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 0)).toNat * a1 := by rw [t80]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have q84 : v84.toNat = v78.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 32)).toNat * a1 := by rw [t84]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have q88 : v88.toNat = v80.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 32)).toNat * a2 := by rw [t88]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have q8c : v8c.toNat = v84.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 28)).toNat * a2 := by rw [t8c]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have q90 : v90.toNat = v88.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 28)).toNat * a3 := by rw [t90]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have q94 : v94.toNat = v8c.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 24)).toNat * a3 := by rw [t94]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have q98 : v98.toNat = v90.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 24)).toNat * a4 := by rw [t98]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qa0 : va0.toNat = (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 0)).toNat * a2 := by rw [ta0]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qa4 : va4.toNat = v94.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 20)).toNat * a4 := by rw [ta4]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qa8 : va8.toNat = v98.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 4)).toNat * a0 := by rw [ta8]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qac : vac.toNat = va0.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 32)).toNat * a3 := by rw [tac]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qb0 : vb0.toNat = vac.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 28)).toNat * a4 := by rw [tb0]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qb4 : vb4.toNat = va8.toNat + va4.toNat / 67108864 := by rw [tb4]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qb8 : vb8.toNat = vb0.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 4)).toNat * a1 := by rw [tb8]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qbc : vbc.toNat = va4.toNat % 67108864 := by rw [tbc]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qc0 : vc0.toNat = (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 0)).toNat * a3 := by rw [tc0]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qc4 : vc4.toNat = vb8.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 8)).toNat * a0 := by rw [tc4]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qc8 : vc8.toNat = vb4.toNat / 67108864 := by rw [tc8]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qcc : vcc.toNat = (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 0)).toNat * a4 := by rw [tcc]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qd4 : vd4.toNat = vc0.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 32)).toNat * a4 := by rw [td4]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qd8 : vd8.toNat = vc4.toNat + vc8.toNat := by rw [td8]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qdc : vdc.toNat = vd4.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 4)).toNat * a2 := by rw [tdc]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qe0 : ve0.toNat = vdc.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 8)).toNat * a1 := by rw [te0]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qe4 : ve4.toNat = vd8.toNat / 67108864 := by rw [te4]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qe8 : ve8.toNat = ve0.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 12)).toNat * a0 := by rw [te8]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qec : vec.toNat = vcc.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 4)).toNat * a3 := by rw [tec]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qf0 : vf0.toNat = vec.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 8)).toNat * a2 := by rw [tf0]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qf4 : vf4.toNat = ve8.toNat + ve4.toNat := by rw [tf4]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qf8 : vf8.toNat = vf0.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 12)).toNat * a1 := by rw [tf8]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have qfc : vfc.toNat = vd8.toNat % 67108864 := by rw [tfc]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have q100 : v100.toNat = vf8.toNat + (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 16)).toNat * a0 := by rw [t100]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have q104 : v104.toNat = vf4.toNat / 67108864 := by rw [t104]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have q108 : v108.toNat = vf4.toNat % 67108864 := by rw [t108]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have q110 : v110.toNat = v100.toNat + v104.toNat := by rw [t110]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have q114 : v114.toNat = v110.toNat / 67108864 := by rw [t114]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have q118 : v118.toNat = v110.toNat % 67108864 := by rw [t118]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have bf4 : vf4.toNat < 2 ^ 58 := by omega
  have b110 : v110.toNat < 36662116890968066 := by omega
  have h114 : v114.toNat < 858993459 := by omega
  have q120 : v120.toNat = v114.toNat + 4 * v114.toNat := by
    rw [t120, Nat.mod_eq_of_lt (show v114.toNat < 4294967296 by omega),
      Nat.mod_eq_of_lt (show v114.toNat * 4 < 4294967296 by omega),
      Nat.mod_eq_of_lt (show v114.toNat + v114.toNat * 4 < 4294967296 by omega),
      Nat.mod_eq_of_lt (show v114.toNat + v114.toNat * 4 < 2 ^ 64 by omega)]
    omega
  have q124 : v124.toNat = vb4.toNat % 67108864 := by rw [t124]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  have q128 : v128.toNat = v120.toNat + vbc.toNat := by rw [t128]; clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128; omega
  clear t78 t80 t84 t88 t8c t90 t94 t98 ta0 ta4 ta8 tac tb0 tb4 tb8 tbc tc0 tc4 tc8 tcc td4 td8 tdc te0 te4 te8 tec tf0 tf4 tf8 tfc t100 t104 t108 t110 t114 t118 t120 t124 t128
  refine reach_ps (ps' := subFlags X2 15#64) (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; rw [hx2]; rfl) ?_
  refine k _ _ hg3 ⟨by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact hx1, by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact hx2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; simp only [oh0, tt4, tt3, tt2, tt1, dd0, dd1, dd2, dd3, dd4, Rw]; omega
  · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; simp only [oh0, tt4, tt3, tt2, tt1, dd0, dd1, dd2, dd3, dd4, Rw]; omega
  · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; simp only [oh0, tt4, tt3, tt2, tt1, dd0, dd1, dd2, dd3, dd4, Rw]; omega
  · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; simp only [oh0, tt4, tt3, tt2, tt1, dd0, dd1, dd2, dd3, dd4, Rw]; omega
  · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; simp only [oh0, tt4, tt3, tt2, tt1, dd0, dd1, dd2, dd3, dd4, Rw]; omega
  · simp only [Nat.reduceAdd]
    rw [read32_write32_ne _ _ 40 36 _ (by decide) (by decide) (by decide), read32_write32_same _ _ 36 _ (by decide)]
    simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
    exact setWidth32_id (by omega)
  · simp only [Nat.reduceAdd]
    rw [read32_write32_same _ _ 40 _ (by decide)]
    simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
    exact setWidth32_id (by omega)
  · simp only [Nat.reduceAdd]
    rw [read32_write32_ne _ _ 40 44 _ (by decide) (by decide) (by decide), read32_write32_ne _ _ 36 44 _ (by decide) (by decide) (by decide), read32_write32_ne _ _ 52 44 _ (by decide) (by decide) (by decide), read32_write32_ne _ _ 48 44 _ (by decide) (by decide) (by decide), read32_write32_same _ _ 44 _ (by decide)]
    simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
    exact setWidth32_id (by omega)
  · simp only [Nat.reduceAdd]
    rw [read32_write32_ne _ _ 40 48 _ (by decide) (by decide) (by decide), read32_write32_ne _ _ 36 48 _ (by decide) (by decide) (by decide), read32_write32_ne _ _ 52 48 _ (by decide) (by decide) (by decide), read32_write32_same _ _ 48 _ (by decide)]
    simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
    exact setWidth32_id (by omega)
  · simp only [Nat.reduceAdd]
    rw [read32_write32_ne _ _ 40 52 _ (by decide) (by decide) (by decide), read32_write32_ne _ _ 36 52 _ (by decide) (by decide) (by decide), read32_write32_same _ _ 52 _ (by decide)]
    simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
    exact setWidth32_id (by omega)

end Poly1305Boringssl.Proof
end

section
/-! # The full-block body (block offsets 0x18..0x68) and the loop step

Loads a 16-byte block from `x1`, splits it into 26-bit limbs (plus `2^24` for the appended
`0x01` byte), adds them to the accumulator limbs in `x8..x12`, then runs `mulSeg`. -/

namespace Poly1305Boringssl.Proof

open Arm64 Arm64.Obj

/-- `n` readable message bytes at `X`, outside the written region. -/
def MsgOk (s0 : State) (X : BitVec 64) (n : Nat) : Prop :=
  ∀ k < n, ¬ W s0 (X + BitVec.ofNat 64 k) ∧ (s0.mem.perm (X + BitVec.ofNat 64 k)).r = true ∧
    s0.mem.isLazyFree (X + BitVec.ofNat 64 k) = false

theorem read32_notW {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64}
    (h : ∀ k < 4, ¬ W s0 (a + BitVec.ofNat 64 k)) : m.read32 a = s0.mem.read32 a := by
  rw [read32_eq, read32_eq, read8_of_notW hm (h 3 (by decide)), read8_of_notW hm (h 2 (by decide)),
    read8_of_notW hm (h 1 (by decide)), read8_of_notW hm (h 0 (by decide))]

theorem ld_lt (x : BitVec 32) : (x.setWidth 64 : BitVec 64).toNat < 2 ^ 32 := by
  have := x.isLt; simp [BitVec.toNat_setWidth]; omega

theorem r_ldpMsg {pl : Placement} {Q : State → Prop} {s0 : State} {pc sp : BitVec 64} {m : Memory}
    {ps : PState} {r : Nat → BitVec 64} {t1 t2 : BitVec 5} {off : Nat} {X : BitVec 64}
    (hrun : s0.status = .Running) (hg : Good pl s0 m)
    (hf : (prog pl).fetchMem m pc =
      some (.ldp .W32 false (.gpr t1) (.gpr t2) (.Offset (.gpr 1#5) (BitVec.ofNat 64 off))))
    (hx : r 1 = X) (hmsg : MsgOk s0 X 16) (hoff : off + 8 ≤ 16 := by decide)
    (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide)
    (h : Reach pl Q (mkS s0 (pc + 4#64) sp m ps
      (upd (upd r t1.toNat ((s0.mem.read32 (X + BitVec.ofNat 64 off)).setWidth 64)) t2.toNat
        ((s0.mem.read32 (X + BitVec.ofNat 64 (off + 4))).setWidth 64)))) :
    Reach pl Q (mkS s0 pc sp m ps r) := by
  have hb : ∀ j, j + 4 ≤ off + 8 → ∀ k < 4, ¬ W s0 (X + BitVec.ofNat 64 j + BitVec.ofNat 64 k) ∧
      (s0.mem.perm (X + BitVec.ofNat 64 j + BitVec.ofNat 64 k)).r = true ∧
      s0.mem.isLazyFree (X + BitVec.ofNat 64 j + BitVec.ofNat 64 k) = false := by
    intro j hj k hk; rw [pc_add]; exact hmsg (j + k) (by omega)
  refine r_ldp32 (a := X + BitVec.ofNat 64 off) hrun hf
    (by rw [rd_gpr _ _ _ _ _ _ _ (by decide)]; exact congrArg (· + _) hx)
    (canRead_notW hg.2.2 (hb off (by omega))) (by rw [pc_add]; exact canRead_notW hg.2.2 (hb (off + 4) (by omega)))
    h1 h2 (h := ?_)
  rw [read32_notW hg.2.2 fun k hk => (hb off (by omega) k hk).1, pc_add,
    read32_notW hg.2.2 fun k hk => (hb (off + 4) (by omega) k hk).1]
  exact h

/-- The 26-bit limbs of a 16-byte block with 32-bit little-endian words `w0..w3`. -/
def lb0 (w0 : Nat) : Nat := w0 % 2 ^ 26
def lb1 (w0 w1 : Nat) : Nat := (w0 + 2 ^ 32 * w1) / 2 ^ 26 % 2 ^ 26
def lb2 (w1 w2 : Nat) : Nat := (w1 + 2 ^ 32 * w2) / 2 ^ 20 % 2 ^ 26
def lb3 (w2 w3 : Nat) : Nat := (w2 + 2 ^ 32 * w3) / 2 ^ 14 % 2 ^ 26

theorem limbs_val (w0 w1 w2 w3 : Nat) (h0 : w0 < 2 ^ 32) (h1 : w1 < 2 ^ 32) (h2 : w2 < 2 ^ 32)
    (h3 : w3 < 2 ^ 32) :
    lb0 w0 + 2 ^ 26 * lb1 w0 w1 + 2 ^ 52 * lb2 w1 w2 + 2 ^ 78 * lb3 w2 w3 + 2 ^ 104 * (w3 / 2 ^ 8) =
      w0 + 2 ^ 32 * w1 + 2 ^ 64 * w2 + 2 ^ 96 * w3 := by
  simp only [lb0, lb1, lb2, lb3]; omega

/-- The message word at byte offset `off` from `X`. -/
abbrev Mw (s0 : State) (X : BitVec 64) (off : Nat) : Nat := (s0.mem.read32 (X + BitVec.ofNat 64 off)).toNat

set_option maxHeartbeats 4000000 in
theorem bodySeg {pl : Placement} {Q : State → Prop} {s0 : State} {sp : BitVec 64} {m : Memory}
    {ps : PState} {r : Nat → BitVec 64} (hrun : s0.status = .Running) (hg : Good pl s0 m)
    (hrs : RSok s0) (hkey : KeyOk s0) {X1 X2 : BitVec 64} (hx1 : r 1 = X1) (hx2 : r 2 = X2)
    (hmsg : MsgOk s0 X1 16) {H0 H1 H2 H3 H4 : Nat}
    (h8 : (r 8).toNat = H0) (h9 : (r 9).toNat = H1) (h10 : (r 10).toNat = H2)
    (h11 : (r 11).toNat = H3) (h12 : (r 12).toNat = H4)
    (hH0 : H0 < 2 ^ 31 + 2 ^ 29 + 2 ^ 27) (hH1 : H1 < 2 ^ 26) (hH2 : H2 < 2 ^ 26)
    (hH3 : H3 < 2 ^ 26) (hH4 : H4 < 2 ^ 26)
    (k : ∀ m' r', Good pl s0 m' → MulPost s0 (X1 + 16#64) (X2 - 16#64) m' r'
      (H0 + lb0 (Mw s0 X1 0)) (lb1 (Mw s0 X1 0) (Mw s0 X1 4) + H1) (lb2 (Mw s0 X1 4) (Mw s0 X1 8) + H2)
      (H3 + lb3 (Mw s0 X1 8) (Mw s0 X1 12)) (H4 + Mw s0 X1 12 / 256 + 16777216) →
      Reach pl Q (mkS s0 (pl.base + 668#64) sp m' (subFlags (X2 - 16#64) 15#64) r')) :
    Reach pl Q (mkS s0 (pl.base + 388#64) sp m ps r) := by
  refine r_ldpMsg hrun hg (f_18 hg) hx1 hmsg (h := ?_)
  refine nx pl.base 388 392 (h := ?_)
  refine r_ldpMsg hrun hg (f_1c hg) hx1 hmsg (h := ?_)
  refine nx pl.base 392 396 (h := ?_)
  refine r_addImm hrun (f_20 hg) (h := ?_)
  refine nx pl.base 396 400 (h := ?_)
  refine r_subImm hrun (f_24 hg) (h := ?_)
  refine nx pl.base 400 404 (h := ?_)
  refine r_orrLsl32 hrun (f_28 hg) (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact ld_lt _) (h := ?_)
  refine nx pl.base 404 408 (h := ?_)
  refine reach_gen fun v28 e28 => ?_
  refine r_andMask hrun (f_2c hg) (h := ?_)
  refine nx pl.base 408 412 (h := ?_)
  refine reach_gen fun v2c e2c => ?_
  refine r_orrLsl32 hrun (f_30 hg) (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact ld_lt _) (h := ?_)
  refine nx pl.base 412 416 (h := ?_)
  refine reach_gen fun v30 e30 => ?_
  refine r_orrLsl32 hrun (f_34 hg) (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact ld_lt _) (h := ?_)
  refine nx pl.base 416 420 (h := ?_)
  refine reach_gen fun v34 e34 => ?_
  refine r_add32 hrun (f_38 hg) (h := ?_)
  refine nx pl.base 420 424 (h := ?_)
  refine reach_gen fun v38 e38 => ?_
  refine r_ubfx hrun (f_3c hg) (h := ?_)
  refine nx pl.base 424 428 (h := ?_)
  refine reach_gen fun v3c e3c => ?_
  refine r_add32 hrun (f_40 hg) (h := ?_)
  refine nx pl.base 428 432 (h := ?_)
  refine reach_gen fun v40 e40 => ?_
  refine r_ubfx hrun (f_44 hg) (h := ?_)
  refine nx pl.base 432 436 (h := ?_)
  refine reach_gen fun v44 e44 => ?_
  refine r_ubfx hrun (f_48 hg) (h := ?_)
  refine nx pl.base 436 440 (h := ?_)
  refine reach_gen fun v48 e48 => ?_
  refine r_add32 hrun (f_4c hg) (h := ?_)
  refine nx pl.base 440 444 (h := ?_)
  refine reach_gen fun v4c e4c => ?_
  refine r_add32 hrun (f_50 hg) (h := ?_)
  refine nx pl.base 444 448 (h := ?_)
  refine reach_gen fun v50 e50 => ?_
  refine r_movz hrun (f_54 hg) (h := ?_)
  refine nx pl.base 448 452 (h := ?_)
  refine r_add32 hrun (f_58 hg) (h := ?_)
  refine nx pl.base 452 456 (h := ?_)
  refine reach_gen fun v58 e58 => ?_
  refine r_add32 hrun (f_5c hg) (h := ?_)
  refine nx pl.base 456 460 (h := ?_)
  refine reach_gen fun v5c e5c => ?_
  refine r_stpH hrun hg (f_60 hg) (h := fun hg1 => ?_)
  refine nx pl.base 460 464 (h := ?_)
  refine r_stpH hrun hg1 (f_64 hg1) (h := fun hg2 => ?_)
  refine nx pl.base 464 468 (h := ?_)
  refine r_strH hrun hg2 (f_68 hg2) (h := fun hg3 => ?_)
  refine nx pl.base 468 472 (h := ?_)
  have i8 : (r 8).toNat % 4294967296 = H0 := by omega
  have i9 : (r 9).toNat % 4294967296 = H1 := by omega
  have i10 : (r 10).toNat % 4294967296 = H2 := by omega
  have i11 : (r 11).toNat % 4294967296 = H3 := by omega
  have i12 : (r 12).toNat % 4294967296 = H4 := by omega
  simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceEqDiff,
    reduceIte, w32_mod, i8, i9, i10, i11, i12, shift32, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at e28 e2c e30 e34 e38 e3c e40 e44 e48 e4c e50 e58 e5c
  have t28 := toNat_eq_of e28
  have t2c := toNat_eq_of e2c
  have t30 := toNat_eq_of e30
  have t34 := toNat_eq_of e34
  have t38 := toNat_eq_of e38
  have t3c := toNat_eq_of e3c
  have t40 := toNat_eq_of e40
  have t44 := toNat_eq_of e44
  have t48 := toNat_eq_of e48
  have t4c := toNat_eq_of e4c
  have t50 := toNat_eq_of e50
  have t58 := toNat_eq_of e58
  have t5c := toNat_eq_of e5c
  have w0 := (s0.mem.read32 (X1 + BitVec.ofNat 64 0)).isLt
  have w1 := (s0.mem.read32 (X1 + BitVec.ofNat 64 4)).isLt
  have w2 := (s0.mem.read32 (X1 + BitVec.ofNat 64 8)).isLt
  have w3 := (s0.mem.read32 (X1 + BitVec.ofNat 64 12)).isLt
  have q28 : v28.toNat = (s0.mem.read32 (X1 + BitVec.ofNat 64 0)).toNat + 4294967296 * (s0.mem.read32 (X1 + BitVec.ofNat 64 4)).toNat := by rw [t28]; clear t28 t2c t30 t34 t38 t3c t40 t44 t48 t4c t50 t58 t5c; omega
  have q2c : v2c.toNat = (s0.mem.read32 (X1 + BitVec.ofNat 64 0)).toNat % 67108864 := by rw [t2c]; clear t28 t2c t30 t34 t38 t3c t40 t44 t48 t4c t50 t58 t5c; omega
  have q30 : v30.toNat = (s0.mem.read32 (X1 + BitVec.ofNat 64 4)).toNat + 4294967296 * (s0.mem.read32 (X1 + BitVec.ofNat 64 8)).toNat := by rw [t30]; clear t28 t2c t30 t34 t38 t3c t40 t44 t48 t4c t50 t58 t5c; omega
  have q34 : v34.toNat = (s0.mem.read32 (X1 + BitVec.ofNat 64 8)).toNat + 4294967296 * (s0.mem.read32 (X1 + BitVec.ofNat 64 12)).toNat := by rw [t34]; clear t28 t2c t30 t34 t38 t3c t40 t44 t48 t4c t50 t58 t5c; omega
  have q38 : v38.toNat = H0 + v2c.toNat := by rw [t38]; clear t28 t2c t30 t34 t38 t3c t40 t44 t48 t4c t50 t58 t5c; omega
  have q3c : v3c.toNat = v28.toNat / 67108864 % 67108864 := by rw [t3c]; clear t28 t2c t30 t34 t38 t3c t40 t44 t48 t4c t50 t58 t5c; omega
  have q40 : v40.toNat = H4 + (s0.mem.read32 (X1 + BitVec.ofNat 64 12)).toNat / 256 := by rw [t40]; clear t28 t2c t30 t34 t38 t3c t40 t44 t48 t4c t50 t58 t5c; omega
  have q44 : v44.toNat = v30.toNat / 1048576 % 67108864 := by rw [t44]; clear t28 t2c t30 t34 t38 t3c t40 t44 t48 t4c t50 t58 t5c; omega
  have q48 : v48.toNat = v34.toNat / 16384 % 67108864 := by rw [t48]; clear t28 t2c t30 t34 t38 t3c t40 t44 t48 t4c t50 t58 t5c; omega
  have q4c : v4c.toNat = v3c.toNat + H1 := by rw [t4c]; clear t28 t2c t30 t34 t38 t3c t40 t44 t48 t4c t50 t58 t5c; omega
  have q50 : v50.toNat = v44.toNat + H2 := by rw [t50]; clear t28 t2c t30 t34 t38 t3c t40 t44 t48 t4c t50 t58 t5c; omega
  have q58 : v58.toNat = H3 + v48.toNat := by rw [t58]; clear t28 t2c t30 t34 t38 t3c t40 t44 t48 t4c t50 t58 t5c; omega
  have q5c : v5c.toNat = v40.toNat + 16777216 := by rw [t5c]; clear t28 t2c t30 t34 t38 t3c t40 t44 t48 t4c t50 t58 t5c; omega
  clear t28 t2c t30 t34 t38 t3c t40 t44 t48 t4c t50 t58 t5c
  refine mulSeg hrun hg3 hrs hkey (X1 := X1 + 16#64) (X2 := X2 - 16#64)
    (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; rw [hx1]; rfl) (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; rw [hx2]; rfl)
    (a0 := H0 + lb0 (Mw s0 X1 0)) (a1 := lb1 (Mw s0 X1 0) (Mw s0 X1 4) + H1)
    (a2 := lb2 (Mw s0 X1 4) (Mw s0 X1 8) + H2) (a3 := H3 + lb3 (Mw s0 X1 8) (Mw s0 X1 12))
    (a4 := H4 + Mw s0 X1 12 / 256 + 16777216)
    (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; simp only [lb0, Mw]; omega) (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; simp only [lb1, Mw]; omega)
    (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; simp only [lb2, Mw]; omega) (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; simp only [lb3, Mw]; omega)
    (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; simp only [Mw]; omega)
    (by simp only [lb0]; omega) (by simp only [lb1]; omega) (by simp only [lb2]; omega)
    (by simp only [lb3]; omega) (by simp only [Mw]; omega) k

end Poly1305Boringssl.Proof
end

section
/-! # The partial final block (block offsets 0x134..0x1c8)

Copies the `n < 16` remaining message bytes to the stack frame, appends `0x01`, zero-fills to 16
bytes, splits the buffer into limbs and jumps back into `mulSeg`. -/

namespace Poly1305Boringssl.Proof

open Arm64 Arm64.Obj

theorem rd_n {s0 : State} {pc sp : BitVec 64} {m : Memory} {ps : PState} {r : Nat → BitVec 64}
    (i : Nat) (h : 1 ≤ i ∧ i ≤ 18 := by decide) :
    (mkS s0 pc sp m ps r).readReg64 (.gpr (BitVec.ofNat 5 i)) = r i := by
  rw [rd_gpr _ _ _ _ _ _ _ (by simp [Ok]; omega)]
  congr 1; simp; omega

theorem upd_n (r : Nat → BitVec 64) (i : Nat) (v : BitVec 64) (h : i < 32 := by decide) :
    upd r (BitVec.ofNat 5 i).toNat v = upd r i v := by
  congr 1; simp; omega

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

theorem toNat_ofNat_lt {r : Nat} (hr : r < 2 ^ 64) : (BitVec.ofNat 64 r).toNat = r := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hr

/-- The stack buffer: bytes `0..c-1` of `f` at `SP`. -/
def BufAt (m : Memory) (SP : BitVec 64) (f : Nat → BitVec 8) (c : Nat) : Prop :=
  ∀ j < c, m.read8 (SP + BitVec.ofNat 64 j) = f j

theorem bufAt_write {m : Memory} {SP : BitVec 64} {f : Nat → BitVec 8} {c : Nat} (hb : BufAt m SP f c)
    (hc : c < 16) : BufAt (m.write8 (SP + BitVec.ofNat 64 c) (f c)) SP f (c + 1) := by
  intro j hj
  rw [read8_write8]
  by_cases e : j = c
  · subst e; simp
  · rw [if_neg (by rw [add_ofNat_inj SP (by omega) (by omega)]; exact e)]
    exact hb j (by omega)

theorem bufAt_len {m : Memory} {SP : BitVec 64} {f : Nat → BitVec 8} {c c' : Nat} (h : c = c')
    (hb : BufAt m SP f c) : BufAt m SP f c' := h ▸ hb

/-- The bytes of the padded final block: the remaining message, `0x01`, then zeros. -/
def padByte (rest : List (BitVec 8)) (j : Nat) : BitVec 8 := (rest ++ [1#8]).getD j 0

section
variable {pl : Placement} {Q : State → Prop} {s0 : State}

/-- The byte-copy loop `0x140..0x150`. -/
theorem copyLoop (hrun : s0.status = .Running) {X1 SP : BitVec 64} {rest : List (BitVec 8)}
    (hSP : SP = s0.sp - 16#64) (hn : rest.length < 16) (hmsg : MsgOk s0 X1 rest.length)
    (hbytes : ∀ j (hj : j < rest.length), s0.mem.read8 (X1 + BitVec.ofNat 64 j) = rest[j])
    {I : Memory → Prop} (hI : ∀ m j v, j < 16 → I m → I (m.write8 (SP + BitVec.ofNat 64 j) v))
    (k : ∀ m' r' ps', Good pl s0 m' → I m' → BufAt m' SP (padByte rest) rest.length →
      r' 1 = X1 → r' 2 = BitVec.ofNat 64 rest.length → r' 8 = BitVec.ofNat 64 rest.length →
      Reach pl Q (mkS s0 (pl.base + 704#64) SP m' ps' r')) :
    ∀ d i m (r : Nat → BitVec 64) ps, d = rest.length - i → i < rest.length → Good pl s0 m → I m →
      BufAt m SP (padByte rest) i → r 1 = X1 → r 2 = BitVec.ofNat 64 rest.length →
      r 8 = BitVec.ofNat 64 i → r 9 = SP →
      Reach pl Q (mkS s0 (pl.base + 684#64) SP m ps r) := by
  intro d
  induction d with
  | zero => intro i _ _ _ hd hi; omega
  | succ d ih =>
    intro i m r ps hd hi hg hIm hb h1 h2 h8 h9
    have hW : W s0 (SP + BitVec.ofNat 64 i) := hSP ▸ W_stk s0 i (by omega)
    have hnW : ¬ W s0 (X1 + BitVec.ofNat 64 i) := (hmsg i hi).1
    have hv : m.read8 (X1 + BitVec.ofNat 64 i) = padByte rest i := by
      rw [read8_of_notW hg.2.2 hnW, hbytes i hi, padByte, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hi, List.getElem?_eq_getElem hi]; rfl
    refine r_ldrbReg (a := X1 + BitVec.ofNat 64 i) hrun (f_140 hg) (by rw [rd_n 1, rd_n 8, h1, h8])
      (canRead_notW hg.2.2 fun k hk => by
        have : k = 0 := by omega
        subst this; simpa using hmsg i hi) (h := ?_)
    refine nx pl.base 684 688 (h := ?_)
    refine r_strbReg (a := SP + BitVec.ofNat 64 i) hrun (f_144 hg)
      (by rw [rd_n 9, rd_n 8, upd_n _ 10, upd_ne _ _ (by decide), upd_ne _ _ (by decide), h9, h8])
      (canWrite_of hg.2.2 fun k hk => by
        have : k = 0 := by omega
        subst this; simpa using hW) (h := ?_)
    refine nx pl.base 688 692 (h := ?_)
    rw [rd_n 10, upd_n _ 10, upd_same, hv,
      show ((padByte rest i).setWidth 64 : BitVec 64).setWidth 8 = padByte rest i by
        apply BitVec.eq_of_toNat_eq; simp]
    have hg1 := Good.write8 hg hW (padByte rest i)
    have hI1 := hI m i (padByte rest i) (by omega) hIm
    refine r_addImm hrun (f_148 hg1) (h := ?_)
    refine nx pl.base 692 696 (h := ?_)
    refine r_cmpReg hrun (f_14c hg1) (h := ?_)
    refine nx pl.base 696 700 (h := ?_)
    rw [upd_n _ 8, show (BitVec.ofNat 5 2).toNat = 2 from rfl, show (BitVec.ofNat 5 8).toNat = 8 from rfl]
    have e8 : upd (upd r 10 ((padByte rest i).setWidth 64)) 8
        (upd r 10 ((padByte rest i).setWidth 64) 8 + (1#12).setWidth 64) 8 =
        BitVec.ofNat 64 (i + 1) := by
      rw [upd_same, upd_ne _ _ (by decide), h8]
      apply BitVec.eq_of_toNat_eq; simp <;> omega
    have e2 : upd (upd r 10 ((padByte rest i).setWidth 64)) 8
        (upd r 10 ((padByte rest i).setWidth 64) 8 + (1#12).setWidth 64) 2 =
        BitVec.ofNat 64 rest.length := by
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), h2]
    rw [e8, e2]
    have hb1 := bufAt_write hb (by omega)
    by_cases he : i + 1 = rest.length
    · refine r_bCond_f hrun (f_150 hg1) (by
        simp [ConditionHolds, subFlags_z, toNat_ofNat_lt (show rest.length < 2 ^ 64 by omega),
          toNat_ofNat_lt (show i + 1 < 2 ^ 64 by omega), he]) ?_
      refine nx pl.base 700 704 (h := ?_)
      rw [he] at hb1
      exact k _ _ _ hg1 hI1 hb1 (by rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), h1]) e2
        (by rw [e8, he])
    · refine r_bCond_t hrun (f_150 hg1) (by
        simp [ConditionHolds, subFlags_z, toNat_ofNat_lt (show rest.length < 2 ^ 64 by omega),
          toNat_ofNat_lt (show i + 1 < 2 ^ 64 by omega)]; omega) ?_
      rw [show pl.base + 700#64 + 0xfffffffffffffff0#64 = pl.base + 684#64 by
        rw [BitVec.add_assoc]; rfl]
      refine ih (i + 1) _ _ _ (by omega) (by omega) hg1 hI1 hb1 ?_ ?_ ?_ ?_
      · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), h1]
      · exact e2
      · exact e8
      · rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), h9]


theorem padByte_zero (rest : List (BitVec 8)) (j : Nat) (h : rest.length < j) : padByte rest j = 0#8 := by
  simp [padByte, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem padByte_one (rest : List (BitVec 8)) : padByte rest rest.length = 1#8 := by
  simp [padByte, List.getD_eq_getElem?_getD]

/-- The zero-fill loop `0x170..0x17c`. -/
theorem zeroLoop (hrun : s0.status = .Running) {SP : BitVec 64} {rest : List (BitVec 8)}
    (hSP : SP = s0.sp - 16#64) {X1 : BitVec 64}
    {I : Memory → Prop} (hI : ∀ m j v, j < 16 → I m → I (m.write8 (SP + BitVec.ofNat 64 j) v))
    (k : ∀ m' r' ps', Good pl s0 m' → I m' → BufAt m' SP (padByte rest) 16 → r' 1 = X1 →
      Reach pl Q (mkS s0 (pl.base + 748#64) SP m' ps' r')) :
    ∀ d i m (r : Nat → BitVec 64) ps, d = 15 - i → rest.length ≤ i → i < 15 → Good pl s0 m → I m →
      BufAt m SP (padByte rest) (i + 1) → r 1 = X1 → r 8 = BitVec.ofNat 64 i → r 9 = SP + BitVec.ofNat 64 1 →
      Reach pl Q (mkS s0 (pl.base + 732#64) SP m ps r) := by
  intro d
  induction d with
  | zero => intro i _ _ _ hd _ hi; omega
  | succ d ih =>
    intro i m r ps hd hn hi hg hIm hb h1 h8 h9
    have hW : W s0 (SP + BitVec.ofNat 64 (i + 1)) := hSP ▸ W_stk s0 (i + 1) (by omega)
    have ha : (mkS s0 (pl.base + 732#64) SP m ps r).readReg64 (.gpr 9#5) +
        (mkS s0 (pl.base + 732#64) SP m ps r).readReg64 (.gpr 8#5) = SP + BitVec.ofNat 64 (i + 1) := by
      rw [rd_n 9, rd_n 8, h9, h8, pc_add, Nat.add_comm]
    refine r_strbReg hrun (f_170 hg) ha (canWrite_of hg.2.2 fun k hk => by
        have : k = 0 := by omega
        subst this; simpa using hW) (h := ?_)
    refine nx pl.base 732 736 (h := ?_)
    rw [rd_xzr, show (0#64 : BitVec 64).setWidth 8 = padByte rest (i + 1) by
      rw [padByte_zero _ _ (by omega)]; rfl]
    have hg1 := Good.write8 hg hW (padByte rest (i + 1))
    have hI1 := hI m (i + 1) (padByte rest (i + 1)) (by omega) hIm
    have hb1 := bufAt_write hb (by omega)
    refine r_addImm hrun (f_174 hg1) (h := ?_)
    refine nx pl.base 736 740 (h := ?_)
    refine r_cmpImm hrun (f_178 hg1) (h := ?_)
    refine nx pl.base 740 744 (h := ?_)
    simp only [show (BitVec.ofNat 5 8).toNat = 8 from rfl]
    have e8 : upd r 8 (r 8 + (1#12).setWidth 64) 8 = BitVec.ofNat 64 (i + 1) := by
      rw [upd_same, h8]
      apply BitVec.eq_of_toNat_eq; simp <;> omega
    rw [e8]
    by_cases he : i + 1 = 15
    · refine r_bCond_f hrun (f_17c hg1) (by
        simp [ConditionHolds, subFlags_c, toNat_ofNat_lt (show i + 1 < 2 ^ 64 by omega)]; omega) ?_
      refine nx pl.base 744 748 (h := ?_)
      exact k _ _ _ hg1 hI1 (bufAt_len (by omega) hb1) (by rw [upd_ne _ _ (by decide), h1])
    · refine r_bCond_t hrun (f_17c hg1) (by
        simp [ConditionHolds, subFlags_c, toNat_ofNat_lt (show i + 1 < 2 ^ 64 by omega)]; omega) ?_
      rw [show pl.base + 744#64 + 0xfffffffffffffff4#64 = pl.base + 732#64 by
        rw [BitVec.add_assoc]; rfl]
      refine ih (i + 1) _ _ _ (by omega) (by omega) (by omega) hg1 hI1 hb1
        (by rw [upd_ne _ _ (by decide), h1]) e8 ?_
      rw [upd_ne _ _ (by decide), h9]

theorem or1_eq (x : BitVec 64) (h : (x &&& 0b1111#64) = 0#64) : x ||| 1#64 = x + BitVec.ofNat 64 1 := by
  have h1 : x &&& 1#64 = 0#64 := by
    have e : (x &&& 15#64) &&& 1#64 = x &&& 1#64 := by
      rw [BitVec.and_assoc, show (15#64 &&& 1#64 : BitVec 64) = 1#64 by decide]
    rw [← e, h]; decide
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ h1]

end

theorem stk_canRead {s0 : State} {m : Memory} (hm : MemOk s0 m) {SP : BitVec 64} (hSP : SP = s0.sp - 16#64)
    (off : Nat) (h : off + 4 ≤ 16 := by decide) : m.canRead (SP + BitVec.ofNat 64 off) 4 = true :=
  canRead_W hm fun k hk => by rw [pc_add, hSP]; exact W_stk s0 _ (by omega)

theorem stk_canRead' {s0 : State} {m : Memory} (hm : MemOk s0 m) {SP : BitVec 64} (hSP : SP = s0.sp - 16#64)
    (off : Nat) (h : off + 8 ≤ 16 := by decide) : m.canRead (SP + BitVec.ofNat 64 off + 4#64) 4 = true := by
  rw [pc_add]; exact stk_canRead hm hSP (off + 4) (by omega)

/-- A 32-bit word of memory `m` at `A + off`, as a number. -/
abbrev Wd (m : Memory) (A : BitVec 64) (off : Nat) : Nat := (m.read32 (A + BitVec.ofNat 64 off)).toNat

set_option maxHeartbeats 4000000 in
/-- The limb extraction of the padded block (`0x180..0x1c8`), then `mulSeg`. -/
theorem tail748 {pl : Placement} {Q : State → Prop} {s0 : State} {SP : BitVec 64} {m : Memory}
    {ps : PState} {r : Nat → BitVec 64} (hrun : s0.status = .Running) (hg : Good pl s0 m)
    (hrs : RSok s0) (hkey : KeyOk s0) (hSP : SP = s0.sp - 16#64) (hal : (SP &&& 0b1111#64) = 0#64)
    {X1 : BitVec 64} (hx1 : r 1 = X1)
    (hH0 : Wd m (X0 s0) 36 < 2 ^ 31 + 2 ^ 29 + 2 ^ 27) (hH1 : Wd m (X0 s0) 40 < 2 ^ 26)
    (hH2 : Wd m (X0 s0) 44 < 2 ^ 26) (hH3 : Wd m (X0 s0) 48 < 2 ^ 26) (hH4 : Wd m (X0 s0) 52 < 2 ^ 26)
    (k : ∀ m' r', Good pl s0 m' → MulPost s0 X1 0#64 m' r'
      (Wd m (X0 s0) 36 + lb0 (Wd m SP 0)) (lb1 (Wd m SP 0) (Wd m SP 4) + Wd m (X0 s0) 40)
      (lb2 (Wd m SP 4) (Wd m SP 8) + Wd m (X0 s0) 44) (Wd m (X0 s0) 48 + lb3 (Wd m SP 8) (Wd m SP 12))
      (Wd m (X0 s0) 52 + Wd m SP 12 / 256) →
      Reach pl Q (mkS s0 (pl.base + 668#64) SP m' (subFlags 0#64 15#64) r')) :
    Reach pl Q (mkS s0 (pl.base + 748#64) SP m ps r) := by
  refine r_ldp32sp hrun (f_180 hg) hal rfl (stk_canRead hg.2.2 hSP 0) (stk_canRead' hg.2.2 hSP 0) (h := ?_)
  refine nx pl.base 748 752 (h := ?_)
  refine r_ldp32sp hrun (f_184 hg) hal rfl (stk_canRead hg.2.2 hSP 8) (stk_canRead' hg.2.2 hSP 8) (h := ?_)
  refine nx pl.base 752 756 (h := ?_)
  refine r_ldpH hrun hg (f_188 hg) (h := ?_)
  refine nx pl.base 756 760 (h := ?_)
  refine r_orrLsl32 hrun (f_18c hg) (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact ld_lt _) (h := ?_)
  refine nx pl.base 760 764 (h := ?_)
  refine reach_gen fun v18c e18c => ?_
  refine r_ldrH hrun hg (f_190 hg) (h := ?_)
  refine nx pl.base 764 768 (h := ?_)
  refine r_andMask hrun (f_194 hg) (h := ?_)
  refine nx pl.base 768 772 (h := ?_)
  refine reach_gen fun v194 e194 => ?_
  refine r_orrLsl32 hrun (f_198 hg) (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact ld_lt _) (h := ?_)
  refine nx pl.base 772 776 (h := ?_)
  refine reach_gen fun v198 e198 => ?_
  refine r_orrLsl32 hrun (f_19c hg) (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact ld_lt _) (h := ?_)
  refine nx pl.base 776 780 (h := ?_)
  refine reach_gen fun v19c e19c => ?_
  refine r_movZero hrun (f_1a0 hg) (h := ?_)
  refine nx pl.base 780 784 (h := ?_)
  refine r_ldpH hrun hg (f_1a4 hg) (h := ?_)
  refine nx pl.base 784 788 (h := ?_)
  refine r_ubfx hrun (f_1a8 hg) (h := ?_)
  refine nx pl.base 788 792 (h := ?_)
  refine reach_gen fun v1a8 e1a8 => ?_
  refine r_ubfx hrun (f_1ac hg) (h := ?_)
  refine nx pl.base 792 796 (h := ?_)
  refine reach_gen fun v1ac e1ac => ?_
  refine r_ubfx hrun (f_1b0 hg) (h := ?_)
  refine nx pl.base 796 800 (h := ?_)
  refine reach_gen fun v1b0 e1b0 => ?_
  refine r_add32 hrun (f_1b4 hg) (h := ?_)
  refine nx pl.base 800 804 (h := ?_)
  refine reach_gen fun v1b4 e1b4 => ?_
  refine r_add32 hrun (f_1b8 hg) (h := ?_)
  refine nx pl.base 804 808 (h := ?_)
  refine reach_gen fun v1b8 e1b8 => ?_
  refine r_add32 hrun (f_1bc hg) (h := ?_)
  refine nx pl.base 808 812 (h := ?_)
  refine reach_gen fun v1bc e1bc => ?_
  refine r_add32 hrun (f_1c0 hg) (h := ?_)
  refine nx pl.base 812 816 (h := ?_)
  refine reach_gen fun v1c0 e1c0 => ?_
  refine r_add32 hrun (f_1c4 hg) (h := ?_)
  refine nx pl.base 816 820 (h := ?_)
  refine reach_gen fun v1c4 e1c4 => ?_
  refine r_b hrun (f_1c8 hg) (h := ?_)
  rw [show pl.base + 820#64 + 0xfffffffffffffea4#64 = pl.base + 472#64 by rw [BitVec.add_assoc]; rfl]
  simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceEqDiff,
    reduceIte, w32_mod, pc_add, shift32, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] at e18c e194 e198 e19c e1a8 e1ac e1b0 e1b4 e1b8 e1bc e1c0 e1c4
  have t18c := toNat_eq_of e18c
  have t194 := toNat_eq_of e194
  have t198 := toNat_eq_of e198
  have t19c := toNat_eq_of e19c
  have t1a8 := toNat_eq_of e1a8
  have t1ac := toNat_eq_of e1ac
  have t1b0 := toNat_eq_of e1b0
  have t1b4 := toNat_eq_of e1b4
  have t1b8 := toNat_eq_of e1b8
  have t1bc := toNat_eq_of e1bc
  have t1c0 := toNat_eq_of e1c0
  have t1c4 := toNat_eq_of e1c4
  have w0 := (m.read32 (SP + BitVec.ofNat 64 0)).isLt
  have w1 := (m.read32 (SP + BitVec.ofNat 64 4)).isLt
  have w2 := (m.read32 (SP + BitVec.ofNat 64 8)).isLt
  have w3 := (m.read32 (SP + BitVec.ofNat 64 12)).isLt
  simp only [Wd] at hH0 hH1 hH2 hH3 hH4
  have q18c : v18c.toNat = (m.read32 (SP + BitVec.ofNat 64 0)).toNat + 4294967296 * (m.read32 (SP + BitVec.ofNat 64 4)).toNat := by rw [t18c]; clear t18c t194 t198 t19c t1a8 t1ac t1b0 t1b4 t1b8 t1bc t1c0 t1c4; omega
  have q194 : v194.toNat = (m.read32 (SP + BitVec.ofNat 64 0)).toNat % 67108864 := by rw [t194]; clear t18c t194 t198 t19c t1a8 t1ac t1b0 t1b4 t1b8 t1bc t1c0 t1c4; omega
  have q198 : v198.toNat = (m.read32 (SP + BitVec.ofNat 64 4)).toNat + 4294967296 * (m.read32 (SP + BitVec.ofNat 64 8)).toNat := by rw [t198]; clear t18c t194 t198 t19c t1a8 t1ac t1b0 t1b4 t1b8 t1bc t1c0 t1c4; omega
  have q19c : v19c.toNat = (m.read32 (SP + BitVec.ofNat 64 8)).toNat + 4294967296 * (m.read32 (SP + BitVec.ofNat 64 12)).toNat := by rw [t19c]; clear t18c t194 t198 t19c t1a8 t1ac t1b0 t1b4 t1b8 t1bc t1c0 t1c4; omega
  have q1a8 : v1a8.toNat = v18c.toNat / 67108864 % 67108864 := by rw [t1a8]; clear t18c t194 t198 t19c t1a8 t1ac t1b0 t1b4 t1b8 t1bc t1c0 t1c4; omega
  have q1ac : v1ac.toNat = v198.toNat / 1048576 % 67108864 := by rw [t1ac]; clear t18c t194 t198 t19c t1a8 t1ac t1b0 t1b4 t1b8 t1bc t1c0 t1c4; omega
  have q1b0 : v1b0.toNat = v19c.toNat / 16384 % 67108864 := by rw [t1b0]; clear t18c t194 t198 t19c t1a8 t1ac t1b0 t1b4 t1b8 t1bc t1c0 t1c4; omega
  have q1b4 : v1b4.toNat = (m.read32 (X0 s0 + BitVec.ofNat 64 36)).toNat + v194.toNat := by rw [t1b4]; clear t18c t194 t198 t19c t1a8 t1ac t1b0 t1b4 t1b8 t1bc t1c0 t1c4; omega
  have q1b8 : v1b8.toNat = (m.read32 (X0 s0 + BitVec.ofNat 64 52)).toNat + (m.read32 (SP + BitVec.ofNat 64 12)).toNat / 256 := by rw [t1b8]; clear t18c t194 t198 t19c t1a8 t1ac t1b0 t1b4 t1b8 t1bc t1c0 t1c4; omega
  have q1bc : v1bc.toNat = v1a8.toNat + (m.read32 (X0 s0 + BitVec.ofNat 64 40)).toNat := by rw [t1bc]; clear t18c t194 t198 t19c t1a8 t1ac t1b0 t1b4 t1b8 t1bc t1c0 t1c4; omega
  have q1c0 : v1c0.toNat = v1ac.toNat + (m.read32 (X0 s0 + BitVec.ofNat 64 44)).toNat := by rw [t1c0]; clear t18c t194 t198 t19c t1a8 t1ac t1b0 t1b4 t1b8 t1bc t1c0 t1c4; omega
  have q1c4 : v1c4.toNat = (m.read32 (X0 s0 + BitVec.ofNat 64 48)).toNat + v1b0.toNat := by rw [t1c4]; clear t18c t194 t198 t19c t1a8 t1ac t1b0 t1b4 t1b8 t1bc t1c0 t1c4; omega
  clear t18c t194 t198 t19c t1a8 t1ac t1b0 t1b4 t1b8 t1bc t1c0 t1c4
  refine mulSeg hrun hg hrs hkey (X1 := X1) (X2 := 0#64)
    (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact hx1) (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte])
    (a0 := Wd m (X0 s0) 36 + lb0 (Wd m SP 0)) (a1 := lb1 (Wd m SP 0) (Wd m SP 4) + Wd m (X0 s0) 40)
    (a2 := lb2 (Wd m SP 4) (Wd m SP 8) + Wd m (X0 s0) 44) (a3 := Wd m (X0 s0) 48 + lb3 (Wd m SP 8) (Wd m SP 12))
    (a4 := Wd m (X0 s0) 52 + Wd m SP 12 / 256)
    (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; simp only [lb0, Wd]; omega) (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; simp only [lb1, Wd]; omega)
    (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; simp only [lb2, Wd]; omega) (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; simp only [lb3, Wd]; omega)
    (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; simp only [Wd]; omega)
    (by simp only [lb0, Wd]; omega) (by simp only [lb1, Wd]; omega) (by simp only [lb2, Wd]; omega)
    (by simp only [lb3, Wd]; omega) (by simp only [Wd]; omega) k

end Poly1305Boringssl.Proof
end

section
/-! # Bytes, words and RFC 8439's block loop

`read32` as a sum of bytes, `leBytesToNum` as a positional sum, and the recursion of `accumulate`. -/

namespace Poly1305Boringssl.Proof

open Arm64 Arm64.Obj

theorem append_toNat {n k : Nat} (x : BitVec n) (y : BitVec k) :
    (x ++ y).toNat = 2 ^ k * x.toNat + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]
  rw [Nat.mul_comm]

/-- A word as a sum of its little-endian bytes. -/
theorem read32_toNat (m : Memory) (a : BitVec 64) :
    (m.read32 a).toNat = (m.read8 (a + BitVec.ofNat 64 0)).toNat +
      256 * (m.read8 (a + BitVec.ofNat 64 1)).toNat + 65536 * (m.read8 (a + BitVec.ofNat 64 2)).toNat +
      16777216 * (m.read8 (a + BitVec.ofNat 64 3)).toNat := by
  rw [read32_eq]
  simp only [append_toNat]
  omega

/-- `Σ_{j < n} g j * 256^j`. -/
def bsum (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bsum g n + g n * 256 ^ n

theorem bsum_succ (g : Nat → Nat) : ∀ n, bsum g (n + 1) = g 0 + 256 * bsum (fun j => g (j + 1)) n
  | 0 => by simp [bsum]
  | n + 1 => by
    rw [bsum, bsum_succ g n, bsum, Nat.pow_succ]
    ring

theorem bsum_zero : ∀ n, bsum (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by simp [bsum, bsum_zero n]

theorem leBytesToNum_bsum : ∀ (bs : List (BitVec 8)) (n : Nat), bs.length ≤ n →
    leBytesToNum bs = bsum (fun j => (bs.getD j 0).toNat) n
  | [], n, _ => by
    have : (fun j => (([] : List (BitVec 8)).getD j 0).toNat) = fun _ => 0 := by funext j; simp
    rw [this, bsum_zero]; rfl
  | b :: bs, n, h => by
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at h; omega⟩
    rw [bsum_succ]
    have := leBytesToNum_bsum bs n (by simp at h; omega)
    simp only [leBytesToNum, List.foldr_cons] at this ⊢
    rw [this]; simp

theorem leBytesToNum_append_one (bs : List (BitVec 8)) : leBytesToNum (bs ++ [1#8]) = leBytesToNum bs + 256 ^ bs.length := by
  induction bs with
  | nil => simp [leBytesToNum]
  | cons b bs ih =>
    simp only [leBytesToNum, List.cons_append, List.foldr_cons, List.length_cons] at ih ⊢
    rw [ih, Nat.pow_succ]; ring

/-- Four words read back as 16 bytes `g 0, ..., g 15`. -/
theorem words_bsum (m : Memory) (A : BitVec 64) (g : Nat → BitVec 8)
    (h : ∀ j < 16, m.read8 (A + BitVec.ofNat 64 j) = g j) :
    (m.read32 (A + BitVec.ofNat 64 0)).toNat + 2 ^ 32 * (m.read32 (A + BitVec.ofNat 64 4)).toNat +
      2 ^ 64 * (m.read32 (A + BitVec.ofNat 64 8)).toNat + 2 ^ 96 * (m.read32 (A + BitVec.ofNat 64 12)).toNat =
      bsum (fun j => (g j).toNat) 16 := by
  simp only [read32_toNat, pc_add, Nat.reduceAdd]
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide),
    h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide),
    h 15 (by decide)]
  simp only [bsum]
  omega

/-! ## RFC 8439's loop -/

theorem accumulate_nil (R a : Nat) : accumulate R a [] = a := rfl

theorem accumulate_short (R a : Nat) (L : List (BitVec 8)) (h0 : 0 < L.length) (h : L.length ≤ 16) :
    accumulate R a L = R * (a + leBytesToNum (L ++ [1#8])) % p1305 := by
  have : (L.length + 15) / 16 = 1 := by omega
  simp [accumulate, this, List.take_of_length_le h]

theorem accumulate_long (R a : Nat) (L : List (BitVec 8)) (h : 16 ≤ L.length) :
    accumulate R a L = accumulate R (R * (a + leBytesToNum (L.take 16 ++ [1#8])) % p1305) (L.drop 16) := by
  have e : (L.length + 15) / 16 = ((L.drop 16).length + 15) / 16 + 1 := by simp; omega
  unfold accumulate
  rw [e, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  simp only [Nat.mul_zero, List.drop_zero]
  congr 1
  funext x y
  rw [List.drop_drop]
  rw [show 16 * y.succ = 16 + 16 * y by omega]

theorem accumulate_mod (R a a' : Nat) (L : List (BitVec 8)) (h : a % p1305 = a' % p1305) :
    accumulate R a L % p1305 = accumulate R a' L % p1305 := by
  by_cases h0 : L.length = 0
  · rw [List.length_eq_zero_iff.mp h0]; simpa [accumulate_nil] using h
  · have hpos : 0 < L.length := by omega
    have step : ∀ b, R * (a + b) % p1305 = R * (a' + b) % p1305 := by
      intro b; rw [Nat.mul_mod, Nat.add_mod, h, ← Nat.add_mod, ← Nat.mul_mod]
    by_cases hl : 16 ≤ L.length
    · rw [accumulate_long R a L hl, accumulate_long R a' L hl, step]
    · rw [accumulate_short R a L hpos (by omega), accumulate_short R a' L hpos (by omega), step]

end Poly1305Boringssl.Proof
end

section
/-! # Control flow of `poly1305_update`: epilogue, tail dispatch, block loop, entry -/

namespace Poly1305Boringssl.Proof

open Arm64 Arm64.Obj

/-- The accumulator words of memory `m` satisfy the `StateOk` bounds. -/
def HOk (s0 : State) (m : Memory) : Prop :=
  Wd m (X0 s0) 36 < 2 ^ 31 + 2 ^ 29 + 2 ^ 27 ∧ Wd m (X0 s0) 40 < 2 ^ 26 ∧ Wd m (X0 s0) 44 < 2 ^ 26 ∧
    Wd m (X0 s0) 48 < 2 ^ 26 ∧ Wd m (X0 s0) 52 < 2 ^ 26

/-- The accumulator of memory `m`. -/
def Hval (s0 : State) (m : Memory) : Nat :=
  Wd m (X0 s0) 36 + 2 ^ 26 * Wd m (X0 s0) 40 + 2 ^ 52 * Wd m (X0 s0) 44 + 2 ^ 78 * Wd m (X0 s0) 48 +
    2 ^ 104 * Wd m (X0 s0) 52

/-- The key `r`. -/
def Rval (s0 : State) : Nat :=
  Rw s0 0 + 2 ^ 26 * Rw s0 4 + 2 ^ 52 * Rw s0 8 + 2 ^ 78 * Rw s0 12 + 2 ^ 104 * Rw s0 16

/-- Returned (`pc = lr`, `sp` restored, everything but scratch registers, flags, memory as at
    entry), with an accumulator congruent to `T`. -/
def Fin (s0 : State) (T : Nat) (sf : State) : Prop :=
  ∃ m r ps, sf = mkS s0 (s0.readReg64 (.gpr 0x1e#5)) s0.sp m ps r ∧ MemOk s0 m ∧ HOk s0 m ∧
    Hval s0 m % p1305 = T % p1305

section
variable {pl : Placement} {s0 : State} {T : Nat}

theorem epi (hrun : s0.status = .Running) {m : Memory} {ps : PState} {r : Nat → BitVec 64}
    (hg : Good pl s0 m) (hh : HOk s0 m) (hv : Hval s0 m % p1305 = T % p1305) :
    Reach pl (Fin s0 T) (mkS s0 (pl.base + 824#64) (s0.sp - 16#64) m ps r) := by
  refine r_addSp hrun (f_1cc hg) ?_
  refine nx pl.base 824 828 (h := ?_)
  refine r_ret hrun (f_1d0 hg) ?_
  rw [BitVec.sub_add_cancel]
  exact reach_done ⟨m, r, ps, rfl, hg.2.2, hh, hv⟩

theorem wd_of_hW {s0 : State} {m : Memory} {off : Nat} {v : BitVec 64} (h : hW s0 m off = v) :
    Wd m (X0 s0) off = v.toNat := by
  rw [← h]; simp only [Wd, hW, BitVec.toNat_setWidth]
  have := (m.read32 (X0 s0 + BitVec.ofNat 64 off)).isLt; omega

/-- What `mulSeg` leaves, as properties of the new accumulator. -/
theorem mulFacts (hkey : KeyOk s0) {X1 X2 : BitVec 64} {m' : Memory} {r' : Nat → BitVec 64}
    {a0 a1 a2 a3 a4 : Nat} (hp : MulPost s0 X1 X2 m' r' a0 a1 a2 a3 a4)
    (ha0 : a0 < 2 ^ 31 + 2 ^ 29 + 2 ^ 27 + 2 ^ 26) (ha1 : a1 < 2 ^ 27) (ha2 : a2 < 2 ^ 27)
    (ha3 : a3 < 2 ^ 27) (ha4 : a4 < 2 ^ 26 + 2 ^ 25) :
    HOk s0 m' ∧
    Hval s0 m' % p1305 = (a0 + 2 ^ 26 * a1 + 2 ^ 52 * a2 + 2 ^ 78 * a3 + 2 ^ 104 * a4) * Rval s0 % p1305 ∧
    r' 8 = hW s0 m' 36 ∧ r' 9 = hW s0 m' 40 ∧ r' 10 = hW s0 m' 44 ∧ r' 11 = hW s0 m' 48 ∧
    r' 12 = hW s0 m' 52 := by
  obtain ⟨_, _, e8, e9, e10, e11, e12, m36, m40, m44, m48, m52⟩ := hp
  obtain ⟨k0, k1, k2, k3, k4, s1, s2, s3, s4⟩ := hkey
  rw [s1, s2, s3, s4] at e8 e9 e10 e11 e12
  have b := mul_bounds a0 a1 a2 a3 a4 (Rw s0 0) (Rw s0 4) (Rw s0 8) (Rw s0 12) (Rw s0 16)
    ha0 ha1 ha2 ha3 ha4 k0 k1 k2 k3 k4
  have w36 := wd_of_hW m36; have w40 := wd_of_hW m40; have w44 := wd_of_hW m44
  have w48 := wd_of_hW m48; have w52 := wd_of_hW m52
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, m36.symm, m40.symm, m44.symm, m48.symm, m52.symm⟩
  · rw [w36, e8]; exact b.2.2.2.2.2
  · rw [w40, e9]; exact Nat.mod_lt _ (by decide)
  · rw [w44, e10]; exact Nat.mod_lt _ (by decide)
  · rw [w48, e11]; exact Nat.mod_lt _ (by decide)
  · rw [w52, e12]; exact Nat.mod_lt _ (by decide)
  · simp only [Hval, Rval]
    rw [w36, w40, w44, w48, w52, e8, e9, e10, e11, e12]
    exact mul_mod a0 a1 a2 a3 a4 (Rw s0 0) (Rw s0 4) (Rw s0 8) (Rw s0 12) (Rw s0 16)

/-- After the last multiply (`x2 = 0`): fall through `b.hi`, take `cbz`, return. -/
theorem fin668z (hrun : s0.status = .Running) {m : Memory} {r : Nat → BitVec 64}
    (hg : Good pl s0 m) (h2 : r 2 = 0#64) (hh : HOk s0 m) (hv : Hval s0 m % p1305 = T % p1305) :
    Reach pl (Fin s0 T) (mkS s0 (pl.base + 668#64) (s0.sp - 16#64) m (subFlags 0#64 15#64) r) := by
  refine r_bCond_f hrun (f_130 hg) (by simp [ConditionHolds, subFlags_c]) ?_
  refine nx pl.base 668 672 (h := ?_)
  refine r_cbz_t hrun (f_134 hg) (by decide) (by rw [show (0x02#5 : BitVec 5).toNat = 2 from rfl, h2]) ?_
  rw [show pl.base + 672#64 + 0x0000000000000098#64 = pl.base + 824#64 by rw [BitVec.add_assoc]; rfl]
  exact epi hrun hg hh hv

end

/-- The stack frame and the state do not overlap (from the precondition's heap). -/
def StkDisj (s0 : State) : Prop :=
  ∀ j < 16, ∀ k < 56, s0.sp - 16#64 + BitVec.ofNat 64 j ≠ X0 s0 + BitVec.ofNat 64 k

/-- The accumulator words of `m` are those of `m0`. -/
def HSame (s0 : State) (m0 m : Memory) : Prop :=
  ∀ i < 5, m.read32 (X0 s0 + BitVec.ofNat 64 (36 + 4 * i)) = m0.read32 (X0 s0 + BitVec.ofNat 64 (36 + 4 * i))

theorem read32_write8_far (m : Memory) (a b : BitVec 64) (v : BitVec 8)
    (h : ∀ k < 4, b + BitVec.ofNat 64 k ≠ a) : (m.write8 a v).read32 b = m.read32 b := by
  rw [read32_eq, read32_eq, read8_write8, read8_write8, read8_write8, read8_write8,
    if_neg (h 3 (by decide)), if_neg (h 2 (by decide)), if_neg (h 1 (by decide)), if_neg (h 0 (by decide))]

theorem hsame_write8 {s0 : State} (hd : StkDisj s0) {m0 : Memory} (j : Nat) (v : BitVec 8) (hj : j < 16)
    {m : Memory} (h : HSame s0 m0 m) : HSame s0 m0 (m.write8 (s0.sp - 16#64 + BitVec.ofNat 64 j) v) := by
  intro i hi
  rw [read32_write8_far _ _ _ _ fun k hk => by rw [pc_add]; exact (hd j hj _ (by omega)).symm]
  exact h i hi

theorem hsame_wd {s0 : State} {m0 m : Memory} (h : HSame s0 m0 m) :
    Wd m (X0 s0) 36 = Wd m0 (X0 s0) 36 ∧ Wd m (X0 s0) 40 = Wd m0 (X0 s0) 40 ∧
    Wd m (X0 s0) 44 = Wd m0 (X0 s0) 44 ∧ Wd m (X0 s0) 48 = Wd m0 (X0 s0) 48 ∧
    Wd m (X0 s0) 52 = Wd m0 (X0 s0) 52 :=
  ⟨by simp only [Wd]; rw [h 0 (by decide)], by simp only [Wd]; rw [h 1 (by decide)],
    by simp only [Wd]; rw [h 2 (by decide)], by simp only [Wd]; rw [h 3 (by decide)],
    by simp only [Wd]; rw [h 4 (by decide)]⟩

section
variable {pl : Placement} {s0 : State} {T : Nat}

/-- From the padded buffer at `0x180` to the return. -/
theorem at748 (hrun : s0.status = .Running) {m : Memory} {ps : PState} {r : Nat → BitVec 64}
    (hg : Good pl s0 m) (hrs : RSok s0) (hkey : KeyOk s0) (hal : (s0.sp - 16#64 &&& 0b1111#64) = 0#64)
    {X1 : BitVec 64} {rest : List (BitVec 8)} (hn : rest.length < 16) (h0 : 0 < rest.length)
    {m0 : Memory} (hI : HSame s0 m0 m) (hb : BufAt m (s0.sp - 16#64) (padByte rest) 16)
    (h1 : r 1 = X1) (hh : HOk s0 m0)
    (hT : accumulate (Rval s0) (Hval s0 m0) rest % p1305 = T % p1305) :
    Reach pl (Fin s0 T) (mkS s0 (pl.base + 748#64) (s0.sp - 16#64) m ps r) := by
  obtain ⟨w36, w40, w44, w48, w52⟩ := hsame_wd hI
  obtain ⟨b0, b1, b2, b3, b4⟩ := hh
  have B0 := (m.read32 (s0.sp - 16#64 + BitVec.ofNat 64 0)).isLt
  have B1 := (m.read32 (s0.sp - 16#64 + BitVec.ofNat 64 4)).isLt
  have B2 := (m.read32 (s0.sp - 16#64 + BitVec.ofNat 64 8)).isLt
  have B3 := (m.read32 (s0.sp - 16#64 + BitVec.ofNat 64 12)).isLt
  refine tail748 hrun hg hrs hkey rfl hal h1 (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun m'' r'' hg'' hp => ?_)
  obtain ⟨hh', hv', -⟩ := mulFacts hkey hp (by simp only [lb0]; omega) (by simp only [lb1]; omega)
    (by simp only [lb2]; omega) (by simp only [lb3]; omega) (by simp only [Wd] at *; omega)
  refine fin668z hrun hg'' hp.2.1 hh' ?_
  have hB := words_bsum m (s0.sp - 16#64) (padByte rest) hb
  have hL := leBytesToNum_bsum (rest ++ [1#8]) 16 (by simp; omega)
  have hlv := limbs_val _ _ _ _ B0 B1 B2 B3
  rw [hv', ← hT, accumulate_short _ _ _ h0 (by omega), Nat.mod_mod]
  rw [Nat.mul_comm (Rval s0)]
  congr 2
  simp only [Hval, Wd, padByte] at *
  omega

end

section
variable {pl : Placement} {s0 : State} {T : Nat}

/-- After the copy loop (`0x154`): store `0x01`, zero-fill if needed, continue at `0x180`. -/
theorem middle704 (hrun : s0.status = .Running) {m : Memory} {ps : PState} {r : Nat → BitVec 64}
    (hg : Good pl s0 m) (hrs : RSok s0) (hkey : KeyOk s0) (hal : (s0.sp - 16#64 &&& 0b1111#64) = 0#64)
    (hd : StkDisj s0) {X1 : BitVec 64} {rest : List (BitVec 8)} (hn : rest.length < 16)
    (h0 : 0 < rest.length) {m0 : Memory} (hI : HSame s0 m0 m)
    (hb : BufAt m (s0.sp - 16#64) (padByte rest) rest.length)
    (h1 : r 1 = X1) (h2 : r 2 = BitVec.ofNat 64 rest.length) (h8 : r 8 = BitVec.ofNat 64 rest.length)
    (hh : HOk s0 m0) (hT : accumulate (Rval s0) (Hval s0 m0) rest % p1305 = T % p1305) :
    Reach pl (Fin s0 T) (mkS s0 (pl.base + 704#64) (s0.sp - 16#64) m ps r) := by
  have hW : W s0 (s0.sp - 16#64 + BitVec.ofNat 64 rest.length) := W_stk s0 _ hn
  refine r_subImm hrun (f_154 hg) (h := ?_)
  refine nx pl.base 704 708 (h := ?_)
  refine r_movSp hrun (f_158 hg) (h := ?_)
  refine nx pl.base 708 712 (h := ?_)
  refine r_cmpImm hrun (f_15c hg) (h := ?_)
  refine nx pl.base 712 716 (h := ?_)
  refine r_movz hrun (f_160 hg) (h := ?_)
  refine nx pl.base 716 720 (h := ?_)
  refine r_strbReg (a := s0.sp - 16#64 + BitVec.ofNat 64 rest.length) hrun (f_164 hg)
    (by rw [rd_n 9, rd_n 2]; simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; rw [h2])
    (canWrite_of hg.2.2 fun k hk => by
      have : k = 0 := by omega
      subst this; simpa using hW) (h := ?_)
  refine nx pl.base 720 724 (h := ?_)
  rw [rd_n 10]
  rw [show (upd (upd (upd r (BitVec.ofNat 5 10).toNat (r (BitVec.ofNat 5 8).toNat - (1#12).setWidth 64))
      (BitVec.ofNat 5 9).toNat (s0.sp - 16#64)) (BitVec.ofNat 5 10).toNat
      ((((1#16).setWidth 64 <<< 0).setWidth 32).setWidth 64) 10).setWidth 8 = padByte rest rest.length by
    rw [padByte_one]; simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; decide]
  have hg1 := Good.write8 hg hW (padByte rest rest.length)
  have hI1 := hsame_write8 hd rest.length (padByte rest rest.length) hn hI
  have hb1 := bufAt_write hb hn
  have e10 : upd (upd r (BitVec.ofNat 5 10).toNat (r (BitVec.ofNat 5 8).toNat - (1#12).setWidth 64))
      (BitVec.ofNat 5 9).toNat (s0.sp - 16#64) (BitVec.ofNat 5 10).toNat = BitVec.ofNat 64 (rest.length - 1) := by
    simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; rw [h8]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  rw [e10]
  by_cases h15 : rest.length = 15
  · refine r_bCond_t hrun (f_168 hg1) (by
      simp [ConditionHolds, subFlags_c, subFlags_z, toNat_ofNat_lt (show rest.length - 1 < 2 ^ 64 by omega)]
      omega) ?_
    rw [show pl.base + 724#64 + 0x0000000000000018#64 = pl.base + 748#64 by rw [BitVec.add_assoc]; rfl]
    exact at748 hrun hg1 hrs hkey hal hn h0 hI1 (bufAt_len (by omega) hb1)
      (by simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact h1) hh hT
  · refine r_bCond_f hrun (f_168 hg1) (by
      simp [ConditionHolds, subFlags_c, subFlags_z, toNat_ofNat_lt (show rest.length - 1 < 2 ^ 64 by omega)]
      omega) ?_
    refine nx pl.base 724 728 (h := ?_)
    refine r_orr1 hrun (f_16c hg1) (h := ?_)
    refine nx pl.base 728 732 (h := ?_)
    refine zeroLoop (rest := rest) (X1 := X1) (I := HSame s0 m0) hrun rfl
      (fun m j v hj hm => hsame_write8 hd j v hj hm)
      (fun m' r' ps' hg' hI' hb' h1' => at748 hrun hg' hrs hkey hal hn h0 hI' hb' h1' hh hT)
      (15 - rest.length) rest.length _ _ _ rfl (le_refl _) (by omega) hg1 hI1 hb1 ?_ ?_ ?_
    · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact h1
    · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact h8
    · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact or1_eq _ hal

/-- At `0x134` with `n < 16` bytes left: return, or process the padded final block. -/
theorem at672 (hrun : s0.status = .Running) {m : Memory} {ps : PState} {r : Nat → BitVec 64}
    (hg : Good pl s0 m) (hrs : RSok s0) (hkey : KeyOk s0) (hal : (s0.sp - 16#64 &&& 0b1111#64) = 0#64)
    (hd : StkDisj s0) {X1 : BitVec 64} {rest : List (BitVec 8)} (hn : rest.length < 16)
    (hmsg : MsgOk s0 X1 rest.length)
    (hbytes : ∀ j (hj : j < rest.length), s0.mem.read8 (X1 + BitVec.ofNat 64 j) = rest[j])
    (hh : HOk s0 m) (hT : accumulate (Rval s0) (Hval s0 m) rest % p1305 = T % p1305)
    (h1 : r 1 = X1) (h2 : r 2 = BitVec.ofNat 64 rest.length) :
    Reach pl (Fin s0 T) (mkS s0 (pl.base + 672#64) (s0.sp - 16#64) m ps r) := by
  have e2 : (0x02#5 : BitVec 5).toNat = 2 := rfl
  by_cases h0 : rest.length = 0
  · refine r_cbz_t hrun (f_134 hg) (by decide) (by rw [e2, h2, h0]) ?_
    rw [show pl.base + 672#64 + 0x0000000000000098#64 = pl.base + 824#64 by rw [BitVec.add_assoc]; rfl]
    rw [List.length_eq_zero_iff.mp h0, accumulate_nil] at hT
    exact epi hrun hg hh hT
  · refine r_cbz_f hrun (f_134 hg) (by decide) (by
      rw [e2, h2]; intro e; apply h0; have := congrArg BitVec.toNat e
      rw [toNat_ofNat_lt (by omega)] at this; simpa using this) ?_
    refine nx pl.base 672 676 (h := ?_)
    refine r_movZero hrun (f_138 hg) (h := ?_)
    refine nx pl.base 676 680 (h := ?_)
    refine r_movSp hrun (f_13c hg) (h := ?_)
    refine nx pl.base 680 684 (h := ?_)
    refine copyLoop (rest := rest) (X1 := X1) (I := HSame s0 m) hrun rfl hn hmsg hbytes
      (fun m j v hj hm => hsame_write8 hd j v hj hm)
      (fun m' r' ps' hg' hI' hb' h1' h2' h8' =>
        middle704 hrun hg' hrs hkey hal hd hn (by omega) hI' hb' h1' h2' h8' hh hT)
      (rest.length - 0) 0 _ _ _ rfl (by omega) hg (fun i _ => rfl) (fun j hj => by omega) ?_ ?_ ?_ ?_
    · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact h1
    · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact h2
    · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
    · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]

end

theorem msgOk_shift {s0 : State} {X : BitVec 64} {n : Nat} (h : MsgOk s0 X (n + 16)) :
    MsgOk s0 (X + 16#64) n := fun k hk => by
  rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, pc_add]; exact h (16 + k) (by omega)

theorem msgOk_mono {s0 : State} {X : BitVec 64} {n n' : Nat} (h : MsgOk s0 X n) (hn : n' ≤ n) :
    MsgOk s0 X n' := fun k hk => h k (by omega)

theorem toNat_hW {s0 : State} {m : Memory} {off : Nat} : (hW s0 m off).toNat = Wd m (X0 s0) off := by
  simp only [hW, Wd, BitVec.toNat_setWidth]
  have := (m.read32 (X0 s0 + BitVec.ofNat 64 off)).isLt; omega

theorem getD_take16 (rest : List (BitVec 8)) (j : Nat) (hj : j < 16) (hl : 16 ≤ rest.length) :
    ((rest.take 16).getD j 0) = rest[j]'(by omega) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hj, List.getElem?_eq_getElem (show j < rest.length by omega)]

section
variable {pl : Placement} {s0 : State} {T : Nat}

/-- The full-block loop, by induction on the remaining length. -/
theorem loop388 (hrun : s0.status = .Running) (hrs : RSok s0) (hkey : KeyOk s0)
    (hal : (s0.sp - 16#64 &&& 0b1111#64) = 0#64) (hd : StkDisj s0) :
    ∀ d (rest : List (BitVec 8)) (X1 : BitVec 64) (m : Memory) (r : Nat → BitVec 64) (ps : PState),
      rest.length ≤ d → 16 ≤ rest.length → rest.length < 2 ^ 64 → Good pl s0 m → MsgOk s0 X1 rest.length →
      (∀ j (hj : j < rest.length), s0.mem.read8 (X1 + BitVec.ofNat 64 j) = rest[j]) →
      HOk s0 m → accumulate (Rval s0) (Hval s0 m) rest % p1305 = T % p1305 →
      r 1 = X1 → r 2 = BitVec.ofNat 64 rest.length →
      r 8 = hW s0 m 36 → r 9 = hW s0 m 40 → r 10 = hW s0 m 44 → r 11 = hW s0 m 48 → r 12 = hW s0 m 52 →
      Reach pl (Fin s0 T) (mkS s0 (pl.base + 388#64) (s0.sp - 16#64) m ps r) := by
  intro d
  induction d with
  | zero => intro rest _ _ _ _ _ hl h16; omega
  | succ d ih =>
    intro rest X1 m r ps hl h16 h64 hg hmsg hbytes hh hT h1 h2 h8 h9 h10 h11 h12
    obtain ⟨b0, b1, b2, b3, b4⟩ := hh
    have W0 := (s0.mem.read32 (X1 + BitVec.ofNat 64 0)).isLt
    have W1 := (s0.mem.read32 (X1 + BitVec.ofNat 64 4)).isLt
    have W2 := (s0.mem.read32 (X1 + BitVec.ofNat 64 8)).isLt
    have W3 := (s0.mem.read32 (X1 + BitVec.ofNat 64 12)).isLt
    refine bodySeg hrun hg hrs hkey h1 h2 (msgOk_mono hmsg h16)
      (by rw [h8, toNat_hW]) (by rw [h9, toNat_hW]) (by rw [h10, toNat_hW]) (by rw [h11, toNat_hW])
      (by rw [h12, toNat_hW]) b0 b1 b2 b3 b4 (fun m' r' hg' hp => ?_)
    obtain ⟨hh', hv', e8, e9, e10, e11, e12⟩ := mulFacts hkey hp (by simp only [lb0]; omega)
      (by simp only [lb1]; omega) (by simp only [lb2]; omega) (by simp only [lb3]; omega)
      (by simp only [Mw] at *; omega)
    -- the new accumulator continues RFC 8439's loop on the rest of the message
    have hB := words_bsum s0.mem X1 (fun j => (rest.take 16).getD j 0) (fun j hj => by
      rw [getD_take16 rest j hj h16]; exact hbytes j (by omega))
    have hL := leBytesToNum_bsum (rest.take 16) 16 (by simp)
    have hA := leBytesToNum_append_one (rest.take 16)
    have hlv := limbs_val _ _ _ _ W0 W1 W2 W3
    have hT' : accumulate (Rval s0) (Hval s0 m') (rest.drop 16) % p1305 = T % p1305 := by
      rw [← hT, accumulate_long _ _ _ h16]
      apply accumulate_mod
      rw [hv', Nat.mod_mod, Nat.mul_comm (Rval s0)]
      congr 2
      simp only [List.length_take, show min 16 rest.length = 16 by omega] at hA
      simp only [Hval, Wd, Mw] at *
      omega
    have hlen : (rest.drop 16).length = rest.length - 16 := by simp
    have hX2 : BitVec.ofNat 64 rest.length - 16#64 = BitVec.ofNat 64 (rest.drop 16).length := by
      rw [hlen]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
    rw [hX2] at hp ⊢
    have hmsg' : MsgOk s0 (X1 + 16#64) (rest.drop 16).length :=
      msgOk_shift (by rw [hlen, Nat.sub_add_cancel h16]; exact hmsg)
    have hbytes' : ∀ j (hj : j < (rest.drop 16).length),
        s0.mem.read8 (X1 + 16#64 + BitVec.ofNat 64 j) = (rest.drop 16)[j] := by
      intro j hj
      rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, pc_add, List.getElem_drop]
      exact hbytes (16 + j) (by simp at hj; omega)
    by_cases hmore : 16 ≤ (rest.drop 16).length
    · refine r_bCond_t hrun (f_130 hg') (by
        simp [ConditionHolds, subFlags_c, subFlags_z, toNat_ofNat_lt (show (rest.drop 16).length < 2 ^ 64 by omega)]
        omega) ?_
      rw [show pl.base + 668#64 + 0xfffffffffffffee8#64 = pl.base + 388#64 by rw [BitVec.add_assoc]; rfl]
      exact ih (rest.drop 16) (X1 + 16#64) m' r' _ (by omega) hmore (by omega) hg' hmsg' hbytes' hh' hT'
        hp.1 hp.2.1 e8 e9 e10 e11 e12
    · refine r_bCond_f hrun (f_130 hg') (by
        simp [ConditionHolds, subFlags_c, subFlags_z, toNat_ofNat_lt (show (rest.drop 16).length < 2 ^ 64 by omega)]
        omega) ?_
      refine nx pl.base 668 672 (h := ?_)
      exact at672 hrun hg' hrs hkey hal hd (by omega) hmsg' hbytes' hh' hT' hp.1 hp.2.1

end

/-- The entry registers as a scratch-register function. -/
def r0 (s0 : State) : Nat → BitVec 64 := fun k => s0.regs.regs (BitVec.ofNat 5 k)

theorem mkS_self (s0 : State) : mkS s0 s0.pc s0.sp s0.mem s0.pstate (r0 s0) = s0 := by
  have hr : mkRegs s0.regs (r0 s0) = s0.regs := by
    cases hs : s0.regs with
    | mk f =>
      simp only [mkRegs, r0, hs]
      congr 1; funext i
      split <;> simp
  simp only [mkS, hr]

theorem r0_eq (s0 : State) (k : Nat) (h : k < 31 := by decide) :
    r0 s0 k = s0.readReg64 (.gpr (BitVec.ofNat 5 k)) := by
  simp only [r0, State.readReg64, RegFile.read]
  have : (BitVec.ofNat 5 k == 31#5) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e
    have := congrArg BitVec.toNat e; simp at this; omega
  simp [this]

theorem reach_of_eq {pl : Placement} {Q : State → Prop} {s s' : State} (e : s' = s)
    (h : Reach pl Q s') : Reach pl Q s := e ▸ h

section
variable {pl : Placement} {s0 : State}

/-- From the entry: `sub sp`, `cmp x2, #16`, then the tail or the loaded loop. -/
theorem entry (hrun : s0.status = .Running) (hpc : s0.pc = pl.base + 364#64) (hg : Good pl s0 s0.mem)
    (hrs : RSok s0) (hkey : KeyOk s0) (hal : (s0.sp - 16#64 &&& 0b1111#64) = 0#64) (hd : StkDisj s0)
    {msg : List (BitVec 8)} (hlen : (s0.readReg64 (.gpr 2#5)).toNat = msg.length)
    (hmsg : MsgOk s0 (s0.readReg64 (.gpr 1#5)) msg.length)
    (hbytes : ∀ j (hj : j < msg.length), s0.mem.read8 (s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 j) = msg[j])
    (hh : HOk s0 s0.mem) :
    Reach pl (Fin s0 (accumulate (Rval s0) (Hval s0 s0.mem) msg)) s0 := by
  have h64 : msg.length < 2 ^ 64 := hlen ▸ (s0.readReg64 (.gpr 2#5)).isLt
  have h2 : r0 s0 2 = BitVec.ofNat 64 msg.length := by
    rw [r0_eq s0 2]; apply BitVec.eq_of_toNat_eq; rw [toNat_ofNat_lt h64]; exact hlen
  have h1 : r0 s0 1 = s0.readReg64 (.gpr 1#5) := r0_eq s0 1
  refine reach_of_eq (show mkS s0 (pl.base + 364#64) s0.sp s0.mem s0.pstate (r0 s0) = s0 by
    rw [← hpc]; exact mkS_self s0) ?_
  refine r_subSp hrun (f_0 hg) ?_
  refine nx pl.base 364 368 (h := ?_)
  refine r_cmpImm hrun (f_4 hg) (h := ?_)
  refine nx pl.base 368 372 (h := ?_)
  rw [show (0x02#5 : BitVec 5).toNat = 2 from rfl, h2]
  by_cases hs : msg.length < 16
  · refine r_bCond_t hrun (f_8 hg) (by simp [ConditionHolds, subFlags_c, toNat_ofNat_lt h64]; omega) ?_
    rw [show pl.base + 372#64 + 0x000000000000012c#64 = pl.base + 672#64 by rw [BitVec.add_assoc]; rfl]
    exact at672 hrun hg hrs hkey hal hd hs hmsg hbytes hh rfl h1 h2
  · refine r_bCond_f hrun (f_8 hg) (by simp [ConditionHolds, subFlags_c, toNat_ofNat_lt h64]; omega) ?_
    refine nx pl.base 372 376 (h := ?_)
    refine r_ldpH hrun hg (f_c hg) (h := ?_)
    refine nx pl.base 376 380 (h := ?_)
    refine r_ldpH hrun hg (f_10 hg) (h := ?_)
    refine nx pl.base 380 384 (h := ?_)
    refine r_ldrH hrun hg (f_14 hg) (h := ?_)
    refine nx pl.base 384 388 (h := ?_)
    refine loop388 hrun hrs hkey hal hd msg.length msg _ s0.mem _ _ (le_refl _) (by omega) h64 hg hmsg
      hbytes hh rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact h1
    · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]; exact h2
    · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
    · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
    · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
    · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
    · simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]

end

end Poly1305Boringssl.Proof
end

section
/-! # Separation-logic glue: heap cells of the precondition, and `modHeap` for the postcondition

`modHeap h m` is `h` with every read-write byte replaced by the byte of memory `m`. If `h` matched
the entry memory and `m` differs only on read-write bytes of `h` (the region `W`), then
`modHeap h m` matches `m`, and it satisfies the postcondition's assertions. -/

namespace Poly1305Boringssl.Proof

open Arm64 Arm64.Obj

def modCell (m : Memory) (a : BitVec 64) : Option HeapCell → Option HeapCell
  | some (.rw _) => some (.rw (m.read8 a))
  | c => c

def modHeap (h : Heap) (m : Memory) : Heap :=
  { h with phys := fun a => modCell m a (h.phys a) }

theorem modCell_none (m : Memory) (a : BitVec 64) : modCell m a none = none := rfl

theorem modHeap_union (h1 h2 : Heap) (m : Memory) :
    modHeap (h1.union h2) m = (modHeap h1 m).union (modHeap h2 m) := by
  apply Heap.ext
  · funext a
    simp only [modHeap, Heap.union]
    rcases h1.phys a with _ | c <;> simp [modCell_none]
    rcases c <;> simp [modCell]
  all_goals rfl

theorem modHeap_disjoint {h1 h2 : Heap} (hd : h1.Disjoint h2) (m : Memory) :
    (modHeap h1 m).Disjoint (modHeap h2 m) := by
  refine ⟨fun a => ?_, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2⟩
  rcases hd.1 a with e | e | ⟨b, e1, e2⟩
  · exact Or.inl (by simp [modHeap, e, modCell_none])
  · exact Or.inr (Or.inl (by simp [modHeap, e, modCell_none]))
  · exact Or.inr (Or.inr ⟨b, by simp [modHeap, e1, modCell], by simp [modHeap, e2, modCell]⟩)

theorem modHeap_empty (m : Memory) : modHeap Heap.empty m = Heap.empty := by
  apply Heap.ext <;> rfl

theorem empty_union (h : Heap) : Heap.empty.union h = h := by
  apply Heap.ext
  · funext a; simp [Heap.union, Heap.empty]
  · funext g k; simp [Heap.union, Heap.empty]
  · funext g k; simp [Heap.union, Heap.empty]
  · funext a; simp [Heap.union, Heap.empty]

theorem union_empty (h : Heap) : h.union Heap.empty = h := by
  apply Heap.ext
  · funext a; simp only [Heap.union, Heap.empty]; split <;> simp_all
  · funext g k; simp only [Heap.union]; split <;> simp_all [Heap.empty]
  · funext g k; simp only [Heap.union]; split <;> simp_all [Heap.empty]
  · funext a; simp [Heap.union, Heap.empty]

theorem disjoint_empty (h : Heap) : h.Disjoint Heap.empty := by
  refine ⟨fun _ => Or.inr (Or.inl rfl), fun _ _ => Or.inr rfl, fun _ _ => Or.inr rfl, ?_, fun _ => Or.inr rfl⟩
  intro _ _ _ _ e
  rcases e with ⟨_, e⟩ | ⟨e, _⟩ <;> cases e

/-! ## Cells -/

theorem cell_union_left {h1 h2 : Heap} {a : BitVec 64} {c : HeapCell} (h : h1.phys a = some c) :
    (h1.union h2).phys a = some c := by
  simp [Heap.union, h]

theorem cell_union_right_rw {h1 h2 : Heap} (hd : h1.Disjoint h2) {a : BitVec 64} {b : BitVec 8}
    (h : h2.phys a = some (.rw b)) : (h1.union h2).phys a = some (.rw b) := by
  rcases hd.1 a with h0 | h0 | ⟨b', e1, e2⟩
  · simp [Heap.union, h0, h]
  · rw [h] at h0; cases h0
  · rw [h] at e2; cases e2

theorem cell_union_right_ro {h1 h2 : Heap} (hd : h1.Disjoint h2) {a : BitVec 64} {b : BitVec 8}
    (h : h2.phys a = some (.ro b)) : (h1.union h2).phys a = some (.ro b) := by
  rcases hd.1 a with h0 | h0 | ⟨b', e1, e2⟩
  · simp [Heap.union, h0, h]
  · rw [h] at h0; cases h0
  · rw [h] at e2; cases e2; simp [Heap.union, e1]

theorem bytes_rw : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap),
    (pointsToBytes a bs).holds h → ∀ i (hi : i < bs.length),
      h.phys (a + BitVec.ofNat 64 i) = some (.rw bs[i])
  | [], _, _, _, i, hi => by simp at hi
  | b :: bs, a, h, hs, i, hi => by
    obtain ⟨h1, h2, hd, rfl, p1, p2⟩ := hs
    cases i with
    | zero =>
      simp only [pointsTo8] at p1; subst p1
      exact cell_union_left (by simp [Heap.singleton])
    | succ i =>
      have := bytes_rw bs (a + 1#64) h2 p2 i (by simp at hi; omega)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm] at this
      exact cell_union_right_rw hd (by simpa using this)

theorem bytes_ro : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap),
    (pointsToBytesRO a bs).holds h → ∀ i (hi : i < bs.length),
      h.phys (a + BitVec.ofNat 64 i) = some (.ro bs[i])
  | [], _, _, _, i, hi => by simp at hi
  | b :: bs, a, h, hs, i, hi => by
    obtain ⟨h1, h2, hd, rfl, p1, p2⟩ := hs
    cases i with
    | zero =>
      simp only [pointsTo8RO] at p1; subst p1
      exact cell_union_left (by simp [Heap.singletonRO])
    | succ i =>
      have := bytes_ro bs (a + 1#64) h2 p2 i (by simp at hi; omega)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm] at this
      exact cell_union_right_ro hd (by simpa using this)

/-- Read-only bytes have no read-write cells: `modHeap` leaves them alone. -/
theorem modHeap_ro : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap) (m : Memory),
    (pointsToBytesRO a bs).holds h → modHeap h m = h
  | [], _, h, m, hs => by
    simp only [pointsToBytesRO, emp] at hs; subst hs; exact modHeap_empty m
  | b :: bs, a, h, m, hs => by
    obtain ⟨h1, h2, hd, rfl, p1, p2⟩ := hs
    rw [modHeap_union, modHeap_ro bs _ h2 m p2]
    simp only [pointsTo8RO] at p1; subst p1
    congr 1
    apply Heap.ext
    · funext x; simp only [modHeap, Heap.singletonRO]; split <;> rfl
    all_goals rfl

/-- `modHeap` of owned bytes: owned bytes holding what `m` holds there. -/
theorem modHeap_bytes : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap) (m : Memory),
    (pointsToBytes a bs).holds h →
      (pointsToBytes a ((List.range bs.length).map fun j => m.read8 (a + BitVec.ofNat 64 j))).holds
        (modHeap h m)
  | [], _, h, m, hs => by
    simp only [pointsToBytes, emp] at hs; subst hs
    simp only [List.length_nil, List.range_zero, List.map_nil, modHeap_empty]; rfl
  | b :: bs, a, h, m, hs => by
    obtain ⟨h1, h2, hd, rfl, p1, p2⟩ := hs
    rw [modHeap_union]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine ⟨_, _, modHeap_disjoint hd m, rfl, ?_, ?_⟩
    · simp only [pointsTo8] at p1 ⊢; subst p1
      apply Heap.ext
      · funext x; simp only [modHeap, Heap.singleton]
        split <;> rename_i e
        · subst e; simp [modCell]
        · rfl
      all_goals rfl
    · have := modHeap_bytes bs (a + 1#64) h2 m p2
      convert this using 3
      funext j
      simp only [Function.comp]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]

theorem modHeap_region (b : BitVec 64) (n : Nat) (mm m : Memory) :
    modHeap (regionHeap b n mm) m = regionHeap b n m := by
  apply Heap.ext
  · funext a; simp only [modHeap, regionHeap]; split <;> rfl
  all_goals rfl

/-- `modHeap h m` matches `m` when `h` matched `s0.mem`, `m` differs from `s0.mem` only on `W`,
    and `W` lies in the read-write cells of `h`. -/
theorem modHeap_matches {s0 : State} {h : Heap} {m : Memory} (hm : h.Matches s0.mem)
    (hok : MemOk s0 m) (hW : ∀ a, W s0 a → ∃ b, h.phys a = some (.rw b)) :
    (modHeap h m).Matches m := by
  have perm_eq : ∀ a, m.perm a = s0.mem.perm a := by
    intro a
    by_cases w : W s0 a
    · rw [(hok.2 a w).1, (hok.2 a w).2.2.2]
    · exact perm_of_notW hok w
  have anon_eq : ∀ a, m.isAnon a = s0.mem.isAnon a := by
    intro a
    by_cases w : W s0 a
    · exact (hok.2 a w).2.2.1
    · simp [Memory.isAnon, hok.1 a w]
  refine ⟨fun a c hc => ?_, hm.2.1, fun a ha => ?_⟩
  · have hca := hm.1 a
    simp only [modHeap] at hc
    by_cases w : W s0 a
    · obtain ⟨b, hb⟩ := hW a w
      rw [hb] at hc; simp only [modCell] at hc; cases hc
      exact ⟨rfl, (hok.2 a w).1, (hok.2 a w).2.1⟩
    · have hcell := hok.1 a w
      have r8 : m.read8 a = s0.mem.read8 a := by simp [Memory.read8, hcell]
      have pm : m.perm a = s0.mem.perm a := by simp [Memory.perm, hcell]
      have lz : m.isLazyFree a = s0.mem.isLazyFree a := by simp [Memory.isLazyFree, hcell]
      rcases e : h.phys a with _ | c'
      · rw [e] at hc; cases hc
      · rw [e] at hc
        have := hca c' e
        rcases c' with b | b | b | _ | _ <;> simp only [modCell] at hc <;> cases hc <;>
          simp only [r8, pm, lz] at this ⊢ <;> first | exact this | exact ⟨trivial, this.2⟩
  · have := hm.2.2 a ha
    rw [perm_eq, anon_eq]; exact this

end Poly1305Boringssl.Proof
end

section
/-! # `poly1305_update` meets its contract: `Poly1305Boringssl.Proof.goal` -/

namespace Poly1305Boringssl.Proof

open Arm64 Arm64.Obj

/-! ## Byte lists and words -/

theorem u32At_eq (L : List (BitVec 8)) (off : Nat) (h : off + 4 ≤ L.length) :
    u32At L off = L[off].toNat + 256 * L[off + 1].toNat + 65536 * L[off + 2].toNat +
      16777216 * L[off + 3].toNat := by
  unfold u32At
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
  simp only [List.take_succ_cons, List.take_zero, leBytesToNum, List.foldr_cons, List.foldr_nil,
    Nat.add_assoc, Nat.reduceAdd]
  omega

theorem u32At_take (L : List (BitVec 8)) (n off : Nat) (h : off + 4 ≤ n) :
    u32At (L.take n) off = u32At L off := by
  unfold u32At
  rw [List.drop_take, List.take_take, show min 4 (n - off) = 4 by omega]

/-- A word of memory whose bytes are those of `L` at `off`. -/
theorem word_eq {m : Memory} {A : BitVec 64} {L : List (BitVec 8)} {off : Nat} (hl : off + 4 ≤ L.length)
    (h : ∀ k (hk : k < 4), m.read8 (A + BitVec.ofNat 64 (off + k)) = L[off + k]'(by omega)) :
    (m.read32 (A + BitVec.ofNat 64 off)).toNat = u32At L off := by
  rw [read32_toNat, u32At_eq L off hl]
  simp only [pc_add]
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]
  rfl

theorem inRegion_eq {b a : BitVec 64} {n : Nat} (h : InRegion b n a) :
    a = b + BitVec.ofNat 64 (a - b).toNat ∧ (a - b).toNat < n := by
  refine ⟨?_, h⟩
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

theorem align16 {x : BitVec 64} (h : ((x &&& 0b1111#64) == 0#64) = true) :
    (x - 16#64 &&& 0b1111#64) = 0#64 := by
  have h' : x &&& 0b1111#64 = 0#64 := by simpa using h
  have e : ∀ y : BitVec 64, (y &&& 0b1111#64).toNat = y.toNat % 16 := by
    intro y
    rw [BitVec.toNat_and, show (0b1111#64 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h'
  rw [e] at this ⊢
  simp [BitVec.toNat_sub] at this ⊢
  omega

theorem fnAddr_update (pl : Placement) :
    boringsslPoly1305Lib.fnAddr pl
      "_ZN12_GLOBAL__N_115poly1305_updateEPNS_17poly1305_state_stEPKhm [boringssl_poly1305]" =
      pl.base + 364#64 := rfl

theorem inRegion_add (b : BitVec 64) (n j : Nat) (hj : j < n) (hn : n < 2 ^ 64) :
    InRegion b n (b + BitVec.ofNat 64 j) := by
  have := inRegion_off b 0 n j (by omega) (by omega) (by omega)
  simpa using this

theorem not_inRegion_low (A : BitVec 64) (k : Nat) (hk : k < 36) :
    ¬ InRegion (A + 36#64) 20 (A + BitVec.ofNat 64 k) := by
  unfold InRegion
  simp [BitVec.toNat_sub, BitVec.toNat_add]
  omega

/-- Everything the machine-level proof needs, read off the precondition's heap. -/
structure PreFacts (pl : Placement) (s0 : State) (st msg : List (BitVec 8)) (h1 : Heap) : Prop where
  good : Good pl s0 s0.mem
  rs : RSok s0
  key : KeyOk s0
  disj : StkDisj s0
  msgok : MsgOk s0 (s0.readReg64 (.gpr 1#5)) msg.length
  bytes : ∀ j (hj : j < msg.length), s0.mem.read8 (s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 j) = msg[j]
  hok : HOk s0 s0.mem
  rval : Rval s0 = limbVal (rLimb st)
  hval : Hval s0 s0.mem = limbVal (hLimb st)
  wdom : ∀ a, W s0 a → ∃ b, h1.phys a = some (.rw b)
  stb : ∀ j (hj : j < 56), j < st.length ∧ s0.mem.read8 (X0 s0 + BitVec.ofNat 64 j) = st[j]!

theorem stateOk_len {st : List (BitVec 8)} (h : StateOk st) : st.length = 56 := h.1

set_option maxHeartbeats 1000000 in
theorem pre_facts {pl : Placement} {s0 : State} {st msg : List (BitVec 8)} {q1 q3 h2 : Heap}
    {mm : Memory} (hP : boringsslPoly1305Lib.Placeable pl) (hCL : (prog pl).CodeLoaded s0.mem)
    (dg : Heap.empty.Disjoint (q1.union (q3.union (regionHeap (s0.sp - BitVec.ofNat 64 16) 16 mm))))
    (d2 : q1.Disjoint (q3.union (regionHeap (s0.sp - BitVec.ofNat 64 16) 16 mm)))
    (d3 : q3.Disjoint (regionHeap (s0.sp - BitVec.ofNat 64 16) 16 mm))
    (hq1 : (pointsToBytes (X0 s0) st).holds q1)
    (hq3 : (pointsToBytesRO (s0.readReg64 (.gpr 1#5)) msg).holds q3)
    (hm : ((Heap.empty.union (q1.union (q3.union (regionHeap (s0.sp - BitVec.ofNat 64 16) 16 mm)))).union
      h2).Matches s0.mem)
    (hst : StateOk st) :
    PreFacts pl s0 st msg (Heap.empty.union (q1.union (q3.union (regionHeap (s0.sp - BitVec.ofNat 64 16) 16 mm)))) := by
  have hlen := stateOk_len hst
  set reg := regionHeap (s0.sp - BitVec.ofNat 64 16) 16 mm with hreg
  set h1 := Heap.empty.union (q1.union (q3.union reg)) with hh1
  -- cells
  have cS1 : ∀ j (hj : j < 56), h1.phys (X0 s0 + BitVec.ofNat 64 j) = some (.rw (st[j]'(by omega))) :=
    fun j hj => cell_union_right_rw dg (cell_union_left (bytes_rw st _ q1 hq1 j (by omega)))
  have cK34 : ∀ j < 16, (q3.union reg).phys (s0.sp - 16#64 + BitVec.ofNat 64 j) =
      some (.rw (mm.read8 (s0.sp - 16#64 + BitVec.ofNat 64 j))) := fun j hj =>
    cell_union_right_rw d3 (by
      simp only [hreg, regionHeap]
      rw [if_pos (inRegion_add _ 16 j hj (by decide))])
  have cK1 : ∀ j < 16, h1.phys (s0.sp - 16#64 + BitVec.ofNat 64 j) =
      some (.rw (mm.read8 (s0.sp - 16#64 + BitVec.ofNat 64 j))) := fun j hj =>
    cell_union_right_rw dg (cell_union_right_rw d2 (cK34 j hj))
  have cM : ∀ k (hk : k < msg.length), (h1.union h2).phys (s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 k) =
      some (.ro msg[k]) := fun k hk =>
    cell_union_left (cell_union_right_ro dg (cell_union_right_ro d2 (cell_union_left (bytes_ro msg _ q3 hq3 k hk))))
  have rwF : ∀ a b, h1.phys a = some (.rw b) →
      s0.mem.read8 a = b ∧ s0.mem.perm a = some Perm.rw ∧ s0.mem.isLazyFree a = false :=
    fun a b hb => hm.1 a _ (cell_union_left hb)
  -- the written region lies in the read-write cells of the precondition
  have wdom : ∀ a, W s0 a → ∃ b, h1.phys a = some (.rw b) := by
    rintro a (w | w)
    · obtain ⟨e, ht⟩ := inRegion_eq w
      rw [e, show (36#64 : BitVec 64) = BitVec.ofNat 64 36 from rfl, pc_add]
      exact ⟨_, cS1 _ (by omega)⟩
    · obtain ⟨e, ht⟩ := inRegion_eq w
      rw [e]; exact ⟨_, cK1 _ ht⟩
  have disj : StkDisj s0 := by
    intro j hj k hk e
    have a1 := bytes_rw st _ q1 hq1 k (by omega)
    have a2 := cK34 j hj
    rw [e] at a2
    rcases d2.1 (X0 s0 + BitVec.ofNat 64 k) with z | z | ⟨b, z1, z2⟩
    · rw [a1] at z; cases z
    · rw [a2] at z; cases z
    · rw [a2] at z2; cases z2
  have notW_low : ∀ k < 36, ¬ W s0 (X0 s0 + BitVec.ofNat 64 k) := by
    rintro k hk (w | w)
    · exact not_inRegion_low _ k hk w
    · obtain ⟨e, ht⟩ := inRegion_eq w
      exact disj _ ht k (by omega) e.symm
  have stb : ∀ j (hj : j < 56), s0.mem.read8 (X0 s0 + BitVec.ofNat 64 j) = st[j]'(by omega) :=
    fun j hj => (rwF _ _ (cS1 j hj)).1
  have wordS : ∀ off, off + 4 ≤ 56 → (s0.mem.read32 (X0 s0 + BitVec.ofNat 64 off)).toNat = u32At st off :=
    fun off ho => word_eq (by omega) fun k hk => stb (off + k) (by omega)
  obtain ⟨_, k0, k1, k2, k3, k4, hs, hh0, hhi⟩ := hst
  have r0 := wordS 0 (by omega); have r4 := wordS 4 (by omega); have r8 := wordS 8 (by omega)
  have r12 := wordS 12 (by omega); have r16 := wordS 16 (by omega); have r20 := wordS 20 (by omega)
  have r24 := wordS 24 (by omega); have r28 := wordS 28 (by omega); have r32 := wordS 32 (by omega)
  have h36 := wordS 36 (by omega); have h40 := wordS 40 (by omega); have h44 := wordS 44 (by omega)
  have h48 := wordS 48 (by omega); have h52 := wordS 52 (by omega)
  have s1 := hs 1 (by decide) (by decide); have s2 := hs 2 (by decide) (by decide)
  have s3 := hs 3 (by decide) (by decide); have s4 := hs 4 (by decide) (by decide)
  have g1 := hhi 1 (by decide) (by decide); have g2 := hhi 2 (by decide) (by decide)
  have g3 := hhi 3 (by decide) (by decide); have g4 := hhi 4 (by decide) (by decide)
  simp only [rLimb, sLimb, hLimb, Nat.reduceMul, Nat.reduceAdd] at k0 k1 k2 k3 k4 s1 s2 s3 s4 hh0 g1 g2 g3 g4
  refine ⟨⟨hP, hCL, ⟨fun a _ => rfl, fun a w => ?_⟩⟩, ?_, ?_, disj, ?_, ?_, ?_, ?_, ?_, wdom, ?_⟩
  · obtain ⟨b, hb⟩ := wdom a w
    have := rwF a b hb
    exact ⟨this.2.1, this.2.2, rfl, this.2.1⟩
  · intro k hk
    have := rwF _ _ (cS1 k (by omega))
    exact ⟨notW_low k hk, by rw [this.2.1]; rfl, this.2.2⟩
  · simp only [KeyOk, Rw]
    rw [r0, r4, r8, r12, r16, r20, r24, r28, r32]
    exact ⟨k0, k1, k2, k3, k4, s1, s2, s3, s4⟩
  · intro k hk
    have := hm.1 _ _ (cM k hk)
    refine ⟨fun w => ?_, this.2.1, this.2.2⟩
    obtain ⟨b, hb⟩ := wdom _ w
    have := cM k hk
    rw [cell_union_left hb] at this; cases this
  · intro j hj
    exact (hm.1 _ _ (cM j hj)).1
  · simp only [HOk, Wd]
    rw [h36, h40, h44, h48, h52]
    exact ⟨hh0, g1, g2, g3, g4⟩
  · simp only [Rval, limbVal, Rw, rLimb, Nat.reduceMul]
    rw [r0, r4, r8, r12, r16]
  · simp only [Hval, limbVal, Wd, hLimb, Nat.reduceMul, Nat.reduceAdd]
    rw [h36, h40, h44, h48, h52]
  · intro j hj
    refine ⟨by omega, ?_⟩
    rw [stb j hj, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl

/-- The pure part of the postcondition for the final state bytes. -/
theorem post_pure {s0 : State} {st msg : List (BitVec 8)} {mF : Memory} {T : Nat}
    (hst : StateOk st) (hok : MemOk s0 mF) (hhF : HOk s0 mF) (hvF : Hval s0 mF % p1305 = T % p1305)
    (hT : T = accumulate (limbVal (rLimb st)) (limbVal (hLimb st)) msg)
    (stb : ∀ j (hj : j < 56), j < st.length ∧ s0.mem.read8 (X0 s0 + BitVec.ofNat 64 j) = st[j]!)
    (rs : RSok s0) :
    let st' := (List.range st.length).map fun j => mF.read8 (X0 s0 + BitVec.ofNat 64 j)
    StateOk st' ∧ st'.take 36 = st.take 36 ∧
      limbVal (hLimb st') % p1305 = accumulate (limbVal (rLimb st)) (limbVal (hLimb st)) msg % p1305 := by
  intro st'
  have hlen := stateOk_len hst
  have hl' : st'.length = 56 := by simp [st', hlen]
  have gst' : ∀ j (hj : j < st'.length), st'[j] = mF.read8 (X0 s0 + BitVec.ofNat 64 j) := by
    intro j hj; simp [st']
  have htake : st'.take 36 = st.take 36 := by
    apply List.ext_getElem (by simp [hl', hlen])
    intro j h1 h2
    have hj : j < 36 := by rw [List.length_take, hl'] at h1; omega
    simp only [List.getElem_take]
    rw [gst' j (by omega), read8_of_notW hok (rs j hj).1,
      (stb j (by omega)).2, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]; rfl
  have hu : ∀ off, off + 4 ≤ 36 → u32At st' off = u32At st off := by
    intro off ho
    rw [← u32At_take st' 36 off ho, htake, u32At_take st 36 off ho]
  have hw : ∀ off, off + 4 ≤ 56 → u32At st' off = (mF.read32 (X0 s0 + BitVec.ofNat 64 off)).toNat := by
    intro off ho
    exact (word_eq (by omega) fun k hk => (gst' (off + k) (by omega)).symm).symm
  have hR : ∀ i, i ≤ 4 → rLimb st' i = rLimb st i := fun i hi => hu (4 * i) (by omega)
  have hS : ∀ i, 1 ≤ i → i ≤ 4 → sLimb st' i = sLimb st i := fun i h1 h2 => hu (16 + 4 * i) (by omega)
  have hH : ∀ i, i ≤ 4 → hLimb st' i = Wd mF (X0 s0) (36 + 4 * i) := fun i hi => hw (36 + 4 * i) (by omega)
  obtain ⟨_, k0, k1, k2, k3, k4, hs, _, _⟩ := hst
  obtain ⟨b0, b1, b2, b3, b4⟩ := hhF
  refine ⟨⟨hl', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, htake, ?_⟩
  · rw [hR 0 (by decide)]; exact k0
  · rw [hR 1 (by decide)]; exact k1
  · rw [hR 2 (by decide)]; exact k2
  · rw [hR 3 (by decide)]; exact k3
  · rw [hR 4 (by decide)]; exact k4
  · intro i h1 h2; rw [hS i h1 h2, hR i h2]; exact hs i h1 h2
  · rw [hH 0 (by decide)]; exact b0
  · intro i h1 h2
    rw [hH i h2]
    interval_cases i
    · exact b1
    · exact b2
    · exact b3
    · exact b4
  · rw [← hT, ← hvF]
    simp only [limbVal, Hval]
    rw [hH 0 (by decide), hH 1 (by decide), hH 2 (by decide), hH 3 (by decide), hH 4 (by decide)]

theorem modHeap_frame {s0 : State} {h1 h2 : Heap} {mF : Memory} (hd : h1.Disjoint h2)
    (hm : (h1.union h2).Matches s0.mem) (hok : MemOk s0 mF)
    (wdom : ∀ a, W s0 a → ∃ b, h1.phys a = some (.rw b)) : modHeap h2 mF = h2 := by
  apply Heap.ext
  · funext a
    simp only [modHeap]
    rcases e : h2.phys a with _ | ⟨b | b | b | _ | _⟩ <;> try rfl
    -- a read-write byte of the frame lies outside `W` and is unchanged
    have h1a : h1.phys a = none := by
      rcases hd.1 a with z | z | ⟨c, z1, z2⟩
      · exact z
      · rw [e] at z; cases z
      · rw [e] at z2; cases z2
    have nw : ¬ W s0 a := fun w => by
      obtain ⟨c, hc⟩ := wdom a w; rw [h1a] at hc; cases hc
    have := hm.1 a _ (cell_union_right_rw hd e)
    simp only [modCell, read8_of_notW hok nw, this.1]
  all_goals rfl

theorem goal :
    internalOk "_ZN12_GLOBAL__N_115poly1305_updateEPNS_17poly1305_state_stEPKhm [boringssl_poly1305]"
      (fun _ => blocksSpec) := by
  refine ⟨by decide, ?_⟩
  intro pl hP x R s0 hpc hrun hpre hal hCL
  obtain ⟨st, msg⟩ := x
  change (prog pl).CodeLoaded s0.mem at hCL
  obtain ⟨H, hH, hm⟩ := hpre
  obtain ⟨h1, h2, hd12, rfl, hpre1, hR⟩ := hH
  obtain ⟨g1, g234, dg, rfl, ⟨rfl, hφ⟩, hrest⟩ := hpre1
  obtain ⟨q1, q34, d2, rfl, hq1, hq34⟩ := hrest
  obtain ⟨q3, q4, d3, rfl, hq3, ⟨mm, rfl⟩⟩ := hq34
  obtain ⟨hst, hlen⟩ := hφ
  have F := pre_facts hP hCL dg d2 d3 hq1 hq3 hm hst
  have hreach := entry hrun (hpc.trans (fnAddr_update pl)) F.good F.rs F.key (align16 hal) F.disj hlen
    F.msgok F.bytes F.hok
  obtain ⟨sf, hsteps, mF, rF, psF, rfl, hok, hhF, hvF⟩ := hreach
  refine ⟨_, hsteps, Or.inl ⟨⟨rfl, rfl, hrun⟩, ⟨rfl, ?_⟩, ?_⟩⟩
  · simp [CalleeSavedPreserved, State.readReg64, mkS, mkRegs, RegFile.read]
  · have hT : accumulate (Rval s0) (Hval s0 s0.mem) msg =
        accumulate (limbVal (rLimb st)) (limbVal (hLimb st)) msg := by rw [F.rval, F.hval]
    have hpure := post_pure hst hok hhF hvF hT F.stb F.rs
    have h2eq := modHeap_frame hd12 hm hok F.wdom
    have D := modHeap_disjoint hd12 mF
    have D2 := modHeap_disjoint d2 mF
    have D3 := modHeap_disjoint d3 mF
    rw [modHeap_union, modHeap_ro msg _ q3 mF hq3, modHeap_region] at D2
    rw [modHeap_ro msg _ q3 mF hq3, modHeap_region] at D3
    rw [h2eq, modHeap_union, modHeap_empty, empty_union, modHeap_union, modHeap_union,
      modHeap_ro msg _ q3 mF hq3, modHeap_region] at D
    refine ⟨modHeap ((Heap.empty.union (q1.union (q3.union
      (regionHeap (s0.sp - BitVec.ofNat 64 16) 16 mm)))).union h2) mF, ?_,
      modHeap_matches hm hok fun a w => by
        obtain ⟨b, hb⟩ := F.wdom a w; exact ⟨b, cell_union_left hb⟩⟩
    rw [modHeap_union, h2eq, modHeap_union, modHeap_empty, empty_union, modHeap_union, modHeap_union,
      modHeap_ro msg _ q3 mF hq3, modHeap_region]
    refine ⟨_, h2, D, rfl, ?_, hR⟩
    refine ⟨modHeap q1 mF, _, D2, rfl, ?_, q3, _, D3, rfl, hq3, mF, rfl⟩
    exact ⟨_, modHeap q1 mF, Heap.empty, disjoint_empty _, (union_empty _).symm,
      modHeap_bytes st _ q1 mF hq1, rfl, hpure⟩

end Poly1305Boringssl.Proof

namespace Poly1305Boringssl

theorem chk_internalOk_poly1305_update :
    internalOk "_ZN12_GLOBAL__N_115poly1305_updateEPNS_17poly1305_state_stEPKhm [boringssl_poly1305]"
      (fun _ => blocksSpec) := Proof.goal

end Poly1305Boringssl

end

theorem solution :
    Poly1305Boringssl.internalOk
      "_ZN12_GLOBAL__N_115poly1305_updateEPNS_17poly1305_state_stEPKhm [boringssl_poly1305]"
      (fun _ => Poly1305Boringssl.blocksSpec) :=
  Poly1305Boringssl.chk_internalOk_poly1305_update
