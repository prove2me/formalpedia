-- Prove2me | solution 1 for Poly1305DebianCt.ctInternalOk_poly1305_blocks
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-26T16:46:52.468803+00:00
-- url     : https://prove2.me/submissions/9ed55677-8dec-41da-ae80-28b796ea5493

import Definitions.Def_Poly1305DebianCt_PlacedObj
import Definitions.Def_Poly1305DebianCt_Spec
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Definitions.Def_Poly1305Libsodium_Spec
import Mathlib.Tactic.ClearExcept
import Definitions.Def_Arm64_Leakage

section
section
section
section

end
end

section
section
/-! # Instruction fetch for the placed `libsodiumDebianOnetimeauth` text block -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtBlocks

open Arm64 Arm64.Obj

/-- The placed program the goal talks about, with extern hooks `X`. -/
def prog (pl : Placement) (X : String → Option (State → State)) : Program :=
  Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.program pl X

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
theorem code_length : Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedCode.length = 2324 := by rfl

theorem patched_length (pl : Placement) : (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patched pl).length = 2324 := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE]
  show (List.map (fun _ => 4) (List.range (Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedCode.length / 4))).sum = 2324
  rw [code_length]; rfl

theorem hook_none {pl : Placement} (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl)
    (X : String → Option (State → State)) {off : Nat} (hoff : off < 2324) :
    (prog pl X).externAt? (pl.base + BitVec.ofNat 64 off) = none := by
  have hl : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.code.length = 2324 := code_length
  have e1 := (hP.text.externs_ok "__stack_chk_fail" (by decide)).2
  have e3 := (hP.text.externs_ok "memset" (by decide)).2
  have e4 := (hP.text.externs_ok "randombytes_buf" (by decide)).2
  have e5 := (hP.text.externs_ok "sodium_memzero" (by decide)).2
  rw [show Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text = Poly1305DebianCt.libsodiumDebianOnetimeauthCtText from rfl, hl]
    at e1 e3 e4 e5
  have hpc : (pl.base + BitVec.ofNat 64 off - pl.base).toNat = off := by
    rw [show pl.base + BitVec.ofNat 64 off - pl.base = BitVec.ofNat 64 off by bv_omega,
      BitVec.toNat_ofNat]; omega
  simp only [prog, Program.externAt?, Program.hookAtOff?, PlacedLib.program, hpc]
  rw [show Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text.externs =
    ["__stack_chk_fail", "memset", "randombytes_buf", "sodium_memzero"] from rfl]
  simp only [List.map_cons, List.map_nil, List.findSome?_cons, List.findSome?_nil, ite_self,
    beq_iff_eq]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

/-- Byte `k < 4` of the word at aligned offset `off` of the placed code. -/
theorem read8_code {pl : Placement} {m : Memory} {X : String → Option (State → State)}
    (hCL : (prog pl X).CodeLoaded m) {off k : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 2324) (hk : k < 4) :
    m.read8 (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl off).extractLsb' (8 * k) 8 ∧
    m.perm (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
  have hl : (prog pl X).code.length = 2324 := patched_length pl
  have h := codeLoaded_cell hCL (off + k) (by omega)
  have ha : pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
      (prog pl X).base + BitVec.ofNat 64 (off + k) := by
    show _ = pl.base + _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [ha]
  refine ⟨?_, h.2⟩
  rw [h.1]
  have ht := take4_drop_patched (blk := Poly1305DebianCt.libsodiumDebianOnetimeauthCtText) (pl := pl) hal
    (by rw [show Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.code = Poly1305DebianCt.libsodiumDebianOnetimeauthCtPlacedCode from rfl,
      code_length]; exact hlen)
  have e1 : (prog pl X).code[off + k]'(by omega) =
      (((Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patched pl).drop off).take 4)[k]'(by
        simp [List.length_take, List.length_drop, patched_length]; omega) := by
    simp only [List.getElem_take, List.getElem_drop]; rfl
  rw [e1]
  simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * k + i < 32 := by omega
  simp [hi, this]; omega

theorem fetch_word {pl : Placement} {m : Memory} (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {X : String → Option (State → State)} (hCL : (prog pl X).CodeLoaded m) {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 2324) :
    (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl off) := by
  have hb4 : pl.base.toNat % 4 = 0 := by
    have := hP.text.base_aligned
    rw [show Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text.align = 32 from rfl] at this
    omega
  have hnw : pl.base.toNat + 2324 ≤ 2 ^ 64 := by
    have := hP.text.no_wrap
    have hl : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.code.length = 2324 := code_length
    rw [show Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.text = Poly1305DebianCt.libsodiumDebianOnetimeauthCtText from rfl, hl] at this
    exact this
  have hpc : (pl.base + BitVec.ofNat 64 off).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : off % 2 ^ 64 = off := Nat.mod_eq_of_lt (by omega)
    have h2 : (pl.base.toNat + off) % 2 ^ 64 = pl.base.toNat + off := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]; omega
  have hlen' : off < 2324 := by omega
  have r0 := read8_code hCL hal hlen (k := 0) (by omega)
  have r1 := read8_code hCL hal hlen (k := 1) (by omega)
  have r2 := read8_code hCL hal hlen (k := 2) (by omega)
  have r3 := read8_code hCL hal hlen (k := 3) (by omega)
  simp only [Program.fetchMem, hook_none hP X hlen', Option.isSome_none, Bool.false_eq_true,
    if_false, hpc, ne_eq, not_true_eq_false]
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

end Poly1305DebianCtBlocks

end
end

section
section
/-! # Abstract machine states and single-step plumbing

Every state reached by `poly1305_blocks` is `mkS s0 pc sp m ps r`: the entry state `s0` with
`pc`, `sp`, memory `m`, flags `ps` and the registers `x1..x17` (given by `r k` for `1 ≤ k ≤ 17`)
replaced. `x0`, `x18..x30` and everything else stay those of `s0`. -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Arm64 Arm64.Obj

/-- Register `k ∈ [1, 17]` is a scratch register of the abstraction. -/
def Ok (i : BitVec 5) : Prop := 1 ≤ i.toNat ∧ i.toNat ≤ 17

instance (i : BitVec 5) : Decidable (Ok i) := inferInstanceAs (Decidable (_ ∧ _))

/-- Update of the scratch register function. -/
def upd (r : Nat → BitVec 64) (k : Nat) (v : BitVec 64) : Nat → BitVec 64 :=
  fun j => if j = k then v else r j

@[simp] theorem upd_same (r : Nat → BitVec 64) (k : Nat) (v : BitVec 64) : upd r k v k = v := by
  simp [upd]

def mkRegs (rf : RegFile) (r : Nat → BitVec 64) : RegFile :=
  ⟨fun i => if 1 ≤ i.toNat ∧ i.toNat ≤ 17 then r i.toNat else rf.regs i⟩

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

theorem rd_hi (i : BitVec 5) (h : 17 < i.toNat) :
    (mkS s0 pc sp m ps r).readReg64 (.gpr i) = s0.readReg64 (.gpr i) := by
  simp only [State.readReg64, mkS, RegFile.read, mkRegs]
  have : ¬ (1 ≤ i.toNat ∧ i.toNat ≤ 17) := by omega
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

theorem step_mkS {pl : Placement} {X : String → Option (State → State)} {s0 : State} {pc sp : BitVec 64} {m : Memory} {ps : PState}
    {r : Nat → BitVec 64} {inst : Instr} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some inst) {s' : State}
    (he : execInstWithSvc (evalSvc Syscall.standard) inst (mkS s0 pc sp m ps r) = s') :
    Step (prog pl X) (mkS s0 pc sp m ps r) s' := by
  have := Step.exec (prog := prog pl X) (s := mkS s0 pc sp m ps r) hrun hf
  rw [Program.evalInst] at this
  rwa [show (prog pl X).svc = Syscall.standard from rfl, he] at this

end Poly1305DebianCtBlocks

end
end

section
section
/-! # Memory: byte writes, the written region, and the memory invariant `MemOk`

The routine writes only the accumulator bytes `[x0 + 24, x0 + 48)` (the region `W`). `MemOk s0 m`: every cell outside `W` is that of `s0.mem`, and
every byte of `W` is mapped read-write (not lazy-free, anonymity unchanged), as in `s0.mem`. -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Arm64.Obj

section write8
variable (m : Memory) (a b : BitVec 64) (v : BitVec 8)

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

/-- The written region: the accumulator bytes. -/
def W (s0 : State) (a : BitVec 64) : Prop :=
  InRegion (X0 s0 + 24#64) 24 a

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
def Good (pl : Placement) (X : String → Option (State → State)) (s0 : State) (m : Memory) : Prop :=
  Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl ∧ (prog pl X).CodeLoaded s0.mem ∧ MemOk s0 m

theorem Good.codeLoaded {pl : Placement} {X : String → Option (State → State)} {s0 : State} {m : Memory}
    (hg : Good pl X s0 m) : (prog pl X).CodeLoaded m :=
  codeLoaded_of hg.2.1 fun a ha => hg.2.2.1 a fun hw => by
    have := (hg.2.2.2 a hw).2.2.2; rw [ha] at this; cases this

theorem Good.write8 {pl : Placement} {X : String → Option (State → State)} {s0 : State} {m : Memory}
    (hg : Good pl X s0 m) {a : BitVec 64} (ha : W s0 a) (v : BitVec 8) : Good pl X s0 (m.write8 a v) :=
  ⟨hg.1, hg.2.1, memOk_write8 hg.2.2 ha v⟩

end Poly1305DebianCtBlocks

end
end

section
section
/-! # The instruction at each address of `poly1305_blocks` (text offsets 0x1a0..0x2ac)

Each lemma is `rfl` after `fetch_word` and `patchedWord_plain` (no relocation lies inside the
function). Lemma `f_<k>` is function offset `k` (hex). -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Arm64 Arm64.Obj

set_option maxRecDepth 100000

theorem patchedWord_plain (pl : Placement) {off : Nat}
    (h : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocAt? off = none) :
    Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl off = Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.wordAt off := by
  simp [CodeBlock.patchedWord, h]

section
variable {pl : Placement} {X : String → Option (State → State)} {s0 : State} {m : Memory}
  (hg : Good pl X s0 m)
include hg

theorem f_0 : (prog pl X).fetchMem m (pl.base + 416#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x07#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000010#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_4 : (prog pl X).fetchMem m (pl.base + 420#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_8 : (prog pl X).fetchMem m (pl.base + 424#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c : (prog pl X).fetchMem m (pl.base + 428#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x03#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000058#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_10 : (prog pl X).fetchMem m (pl.base + 432#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W32) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x03#5) 0x000#12 false) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_14 : (prog pl X).fetchMem m (pl.base + 436#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.ShiftType.LSL) 2) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_18 : (prog pl X).fetchMem m (pl.base + 440#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000020#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1c : (prog pl X).fetchMem m (pl.base + 444#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 2) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_20 : (prog pl X).fetchMem m (pl.base + 448#64) = some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINC) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.CondCode.NE)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_24 : (prog pl X).fetchMem m (pl.base + 452#64) = some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 62 61) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_28 : (prog pl X).fetchMem m (pl.base + 456#64) = some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) 62 61) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_2c : (prog pl X).fetchMem m (pl.base + 460#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x05#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.gpr 0x01#5) 0x0000000000000010#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_30 : (prog pl X).fetchMem m (pl.base + 464#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x04#5) 0x00000fffffffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_34 : (prog pl X).fetchMem m (pl.base + 468#64) = some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x04#5) 44) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_38 : (prog pl X).fetchMem m (pl.base + 472#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) 0x00000fffffffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_3c : (prog pl X).fetchMem m (pl.base + 476#64) = some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x05#5) 24) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_40 : (prog pl X).fetchMem m (pl.base + 480#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_44 : (prog pl X).fetchMem m (pl.base + 484#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_48 : (prog pl X).fetchMem m (pl.base + 488#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x07#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_4c : (prog pl X).fetchMem m (pl.base + 492#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_50 : (prog pl X).fetchMem m (pl.base + 496#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_54 : (prog pl X).fetchMem m (pl.base + 500#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_58 : (prog pl X).fetchMem m (pl.base + 504#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_5c : (prog pl X).fetchMem m (pl.base + 508#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x10#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_60 : (prog pl X).fetchMem m (pl.base + 512#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_64 : (prog pl X).fetchMem m (pl.base + 516#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_68 : (prog pl X).fetchMem m (pl.base + 520#64) = some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x11#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_6c : (prog pl X).fetchMem m (pl.base + 524#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_70 : (prog pl X).fetchMem m (pl.base + 528#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_74 : (prog pl X).fetchMem m (pl.base + 532#64) = some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x0f#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_78 : (prog pl X).fetchMem m (pl.base + 536#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_7c : (prog pl X).fetchMem m (pl.base + 540#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_80 : (prog pl X).fetchMem m (pl.base + 544#64) = some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x0e#5) 44) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_84 : (prog pl X).fetchMem m (pl.base + 548#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_88 : (prog pl X).fetchMem m (pl.base + 552#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x10#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_8c : (prog pl X).fetchMem m (pl.base + 556#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_90 : (prog pl X).fetchMem m (pl.base + 560#64) = some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x11#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_94 : (prog pl X).fetchMem m (pl.base + 564#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_98 : (prog pl X).fetchMem m (pl.base + 568#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_9c : (prog pl X).fetchMem m (pl.base + 572#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a0 : (prog pl X).fetchMem m (pl.base + 576#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x11#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a4 : (prog pl X).fetchMem m (pl.base + 580#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x0e#5) 0x00000fffffffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a8 : (prog pl X).fetchMem m (pl.base + 584#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_ac : (prog pl X).fetchMem m (pl.base + 588#64) = some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x03#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b0 : (prog pl X).fetchMem m (pl.base + 592#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b4 : (prog pl X).fetchMem m (pl.base + 596#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b8 : (prog pl X).fetchMem m (pl.base + 600#64) = some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINC) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x07#5) (Arm64.CondCode.CC)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_bc : (prog pl X).fetchMem m (pl.base + 604#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c0 : (prog pl X).fetchMem m (pl.base + 608#64) = some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x07#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c4 : (prog pl X).fetchMem m (pl.base + 612#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x06#5) 0x00000fffffffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c8 : (prog pl X).fetchMem m (pl.base + 616#64) = some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x06#5) 44) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_cc : (prog pl X).fetchMem m (pl.base + 620#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d0 : (prog pl X).fetchMem m (pl.base + 624#64) = some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d4 : (prog pl X).fetchMem m (pl.base + 628#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x06#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d8 : (prog pl X).fetchMem m (pl.base + 632#64) = some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINC) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) (Arm64.CondCode.CC)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_dc : (prog pl X).fetchMem m (pl.base + 636#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x10#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e0 : (prog pl X).fetchMem m (pl.base + 640#64) = some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x05#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e4 : (prog pl X).fetchMem m (pl.base + 644#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x04#5) 0x000003ffffffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e8 : (prog pl X).fetchMem m (pl.base + 648#64) = some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x04#5) 42) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_ec : (prog pl X).fetchMem m (pl.base + 652#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSL) 2) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f0 : (prog pl X).fetchMem m (pl.base + 656#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x11#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f4 : (prog pl X).fetchMem m (pl.base + 660#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x03#5) 0x00000fffffffffff#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f8 : (prog pl X).fetchMem m (pl.base + 664#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSR) 44) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_fc : (prog pl X).fetchMem m (pl.base + 668#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_100 : (prog pl X).fetchMem m (pl.base + 672#64) = some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0xffffffffffffff2c#64) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_104 : (prog pl X).fetchMem m (pl.base + 676#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x03#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000018#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_108 : (prog pl X).fetchMem m (pl.base + 680#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0f#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000028#64)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_10c : (prog pl X).fetchMem m (pl.base + 684#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) := by
  rw [fetch_word hg.1 hg.codeLoaded (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

end

end Poly1305DebianCtBlocks

end
end

section
section
/-! # One reachability lemma per instruction shape of `poly1305_blocks`

`Reach pl X Q s`: from `s` the placed program reaches a state satisfying `Q`. Each `r_*` lemma
reduces `Reach` at an abstract state to `Reach` at its successor. Register indices are generic
(`Ok` side conditions are discharged by `decide`). Values written to registers are stated as
`BitVec.ofNat 64 (Nat expression in the operands' toNat)`. -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Arm64.Obj

theorem pc_add (b : BitVec 64) (x y : Nat) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y = b + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

section
variable (svc : State → State) (s : State)
theorem ex_addSubImm (w : RegWidth) (op : AddSubOp) (rd rn : Reg) (imm : BitVec 12) (sh : Bool) :
    execInstWithSvc svc (.addSubImm w op rd rn imm sh) s = execAddSubImm w op rd rn imm sh s := rfl
theorem ex_addSubShift (w : RegWidth) (op : AddSubOp) (rd rn rm : Reg) (sh : ShiftType) (a : Nat) :
    execInstWithSvc svc (.addSubShift w op rd rn rm sh a) s = execAddSubShift w op rd rn rm sh a s := rfl
theorem ex_addSubCarry (w : RegWidth) (op : AddSubOp) (rd rn rm : Reg) :
    execInstWithSvc svc (.addSubCarry w op rd rn rm) s = execAddSubCarry w op rd rn rm s := rfl
theorem ex_logicalImm (w : RegWidth) (op : LogicalOp) (rd rn : Reg) (mask : BitVec 64) :
    execInstWithSvc svc (.logicalImm w op rd rn mask) s = execLogicalImm w op rd rn mask s := rfl
theorem ex_bitfield (w : RegWidth) (op : BitfieldOp) (rd rn : Reg) (a b : Nat) :
    execInstWithSvc svc (.bitfield w op rd rn a b) s = execBitfield w op rd rn a b s := rfl
theorem ex_dataProc3 (w : RegWidth) (op : DataProc3Op) (rd rn rm ra : Reg) :
    execInstWithSvc svc (.dataProc3 w op rd rn rm ra) s = execDataProc3 w op rd rn rm ra s := rfl
theorem ex_condSelect (w : RegWidth) (op : CondSelectOp) (rd rn rm : Reg) (c : CondCode) :
    execInstWithSvc svc (.condSelect w op rd rn rm c) s = execCondSelect w op rd rn rm c s := rfl
theorem ex_extr (rd rn rm : Reg) (lsb : Nat) :
    execInstWithSvc svc (.extr .W64 rd rn rm lsb) s =
      (s.writeReg .W64 rd (((s.readReg64 rn ++ s.readReg64 rm) >>> (lsb % 64)).truncate 64)).advancePC :=
  rfl
theorem ex_bCond (c : CondCode) (off : BitVec 64) :
    execInstWithSvc svc (.bCond c off) s =
      if ConditionHolds c s.pstate then s.setPC (s.pc + off) else s.advancePC := rfl
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

/-- The value of the carry flag as a number. -/
def cv (b : Bool) : Nat := if b then 1 else 0

theorem extr_nat (n k lsb : Nat) (h : lsb ≤ 64) :
    (n * 2 ^ 64 + k) / 2 ^ lsb = k / 2 ^ lsb + n * 2 ^ (64 - lsb) := by
  have e : 2 ^ 64 = 2 ^ lsb * 2 ^ (64 - lsb) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.add_comm, Nat.mul_left_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]

variable {pl : Placement} {X : String → Option (State → State)} {Q : State → Prop} {s0 : State}
  {pc sp : BitVec 64} {m : Memory} {ps : PState} {r : Nat → BitVec 64}

/-! ## Arithmetic and logic -/

/-! ## Branches -/

/-! ## Loads and stores (64-bit) -/

/-! ## Instructions only the GCC build uses -/

end Poly1305DebianCtBlocks

end
end

section
section
/-! # The arithmetic of one block, independent of the machine

Radix `2^44` limbs (44, 44, 42 bits). `a0 a1 a2`: the limbs of `h + block + hibit` (unreduced);
`r0 r1 r2`: the key limbs, `s1 = 20 r1`, `s2 = 20 r2`. The code forms the column sums
`D0 D1 D2` from 64 × 64 → 128-bit products, carries (`E1`, `E2`), folds the top carry back
times 5 (`F`), and leaves the new limbs `N0 N1 N2`. -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)
open Poly1305Boringssl

section
variable (a0 a1 a2 r0 r1 r2 : Nat)

end

end Poly1305DebianCtBlocks

end
end

section
section
/-! # Chain helpers: pc normalization, naming computed values, carries as numbers -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Arm64.Obj

end Poly1305DebianCtBlocks

end
end

section
section
/-! # One iteration of the block loop (function offsets 0x2c..0xf8)

Entered at `0x2c` with the message pointer in `x1`, the key limbs `r0, r1, r2` in `x8, x9, x12`,
`s1 = 20 r1`, `s2 = 20 r2` in `x11, x10`, the hibit flag (`0` or `1`) in `x13` and the accumulator
limbs `h0, h1, h2` in `x7, x3, x15`; leaves the new limbs in the same registers and `x1 + 16` in
`x1` at `0xfc` (the loop test `cmp x1, x2`). `x2` and the key registers are untouched. -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Arm64 Arm64.Obj

end Poly1305DebianCtBlocks

end
end

section
section
/-! # 64-bit words over byte writes; addresses of the state -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

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
theorem W_h (s0 : State) (x : Nat) (h1 : 24 ≤ x) (h2 : x < 48) : W s0 (X0 s0 + BitVec.ofNat 64 x) := by
  have := inRegion_off (X0 s0) 24 24 x h1 (by omega) (by omega)
  unfold W; simpa using this

theorem write64_eq (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    m.write64 a v = (((((((m.write8 (a + BitVec.ofNat 64 0) (v.extractLsb' 0 8)).write8
      (a + BitVec.ofNat 64 1) (v.extractLsb' 8 8)).write8 (a + BitVec.ofNat 64 2) (v.extractLsb' 16 8)).write8
      (a + BitVec.ofNat 64 3) (v.extractLsb' 24 8)).write8 (a + BitVec.ofNat 64 4) (v.extractLsb' 32 8)).write8
      (a + BitVec.ofNat 64 5) (v.extractLsb' 40 8)).write8 (a + BitVec.ofNat 64 6) (v.extractLsb' 48 8)).write8
      (a + BitVec.ofNat 64 7) (v.extractLsb' 56 8) := rfl

theorem good_write64 {pl : Placement} {X : String → Option (State → State)} {s0 : State}
    {m : Memory} (hg : Good pl X s0 m) {a : BitVec 64} (ha : ∀ k < 8, W s0 (a + BitVec.ofNat 64 k))
    (v : BitVec 64) : Good pl X s0 (m.write64 a v) := by
  rw [write64_eq]
  exact Good.write8 (Good.write8 (Good.write8 (Good.write8 (Good.write8 (Good.write8
    (Good.write8 (Good.write8 hg (ha 0 (by decide)) _) (ha 1 (by decide)) _) (ha 2 (by decide)) _)
    (ha 3 (by decide)) _) (ha 4 (by decide)) _) (ha 5 (by decide)) _) (ha 6 (by decide)) _)
    (ha 7 (by decide)) _

end Poly1305DebianCtBlocks

end
end

section
section
/-! # Byte lists: the block loop's specification `blocksAcc`, little-endian words -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Poly1305Boringssl

end Poly1305DebianCtBlocks

end
end

section
section
/-! # The entry facts and the prologue of `poly1305_blocks` (function offsets 0x00..0x28) -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)
open Arm64 Arm64.Obj Poly1305Boringssl

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
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e; have := congrArg BitVec.toNat e; simp at this; omega
  simp [this]

section helpers
variable {s0 : State} {m : Memory}

theorem h_canWrite (hm : MemOk s0 m) (off : Nat) (h1 : 24 ≤ off) (h2 : off + 8 ≤ 48) :
    m.canWrite (X0 s0 + BitVec.ofNat 64 off) 8 = true :=
  canWrite_of hm fun k hk => by rw [pc_add]; exact W_h s0 _ (by omega) (by omega)

theorem h_canRead (hm : MemOk s0 m) (off : Nat) (h1 : 24 ≤ off) (h2 : off + 8 ≤ 48) :
    m.canRead (X0 s0 + BitVec.ofNat 64 off) 8 = true :=
  canRead_W hm fun k hk => by rw [pc_add]; exact W_h s0 _ (by omega) (by omega)

theorem add8 (a : BitVec 64) (x : Nat) : a + BitVec.ofNat 64 x + 8#64 = a + BitVec.ofNat 64 (x + 8) :=
  pc_add a x 8

theorem good_h {pl : Placement} {X : String → Option (State → State)} (hg : Good pl X s0 m)
    (off : Nat) (h1 : 24 ≤ off) (h2 : off + 8 ≤ 48) (v : BitVec 64) :
    Good pl X s0 (m.write64 (X0 s0 + BitVec.ofNat 64 off) v) :=
  good_write64 hg (fun k hk => by rw [pc_add]; exact W_h s0 _ (by omega) (by omega)) v

end helpers

variable {pl : Placement} {X : String → Option (State → State)} {Q : State → Prop} {s0 : State}

end Poly1305DebianCtBlocks

end
end

section
section
/-! # The epilogue (function offsets 0x104..0x10c) and the block loop (induction on the
remaining message; loop test `cmp x1, x2; b.ne` at 0xfc..0x100) -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)
open Arm64 Arm64.Obj Poly1305Boringssl

variable {pl : Placement} {X : String → Option (State → State)} {s0 : State}

/-- The message bytes at `X1`: outside `W`, readable at entry. -/
def MsgOk (s0 : State) (X1 : BitVec 64) (n : Nat) : Prop :=
  ∀ j < n, ¬ W s0 (X1 + BitVec.ofNat 64 j) ∧ (s0.mem.perm (X1 + BitVec.ofNat 64 j)).r = true ∧
    s0.mem.isLazyFree (X1 + BitVec.ofNat 64 j) = false

end Poly1305DebianCtBlocks

end
end

section
section
/-! # Separation-logic glue: heap cells of the precondition, and `modHeap` for the postcondition

`modHeap h m` is `h` with every read-write byte replaced by the byte of memory `m`. If `h` matched
the entry memory and `m` differs only on read-write bytes of `h` (the region `W`), then
`modHeap h m` matches `m`, and it satisfies the postcondition's assertions. -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Arm64.Obj

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

end Poly1305DebianCtBlocks

end
end

section
section
/-! # `poly1305_blocks` meets `blocksSpec`: `Poly1305DebianCtBlocks.goal` -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)
open Arm64 Arm64.Obj Poly1305Boringssl

variable {pl : Placement} {X : String → Option (State → State)} {s0 : State}

/-- Two disjoint heaps do not both own a byte when one owns it read-write. -/
theorem disj_rw {h h' : Heap} (hd : h.Disjoint h') {a : BitVec 64} {b : BitVec 8} {c : HeapCell}
    (h1 : h.phys a = some (.rw b)) (h2 : h'.phys a = some c) : False := by
  rcases hd.1 a with z | z | ⟨_, z1, z2⟩
  · rw [h1] at z; cases z
  · rw [h2] at z; cases z
  · rw [h1] at z1; cases z1

theorem inRegion_eq {b a : BitVec 64} {n : Nat} (h : InRegion b n a) :
    a = b + BitVec.ofNat 64 (a - b).toNat ∧ (a - b).toNat < n := by
  refine ⟨?_, h⟩
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

theorem not_inRegion_h (A : BitVec 64) (k : Nat) (hk : k < 24 ∨ (48 ≤ k ∧ k < 2 ^ 32)) :
    ¬ InRegion (A + 24#64) 24 (A + BitVec.ofNat 64 k) := by
  unfold InRegion
  simp [BitVec.toNat_sub, BitVec.toNat_add]
  omega

/-- A read-write or read-only cell. -/
def Own (c : Option HeapCell) (b : BitVec 8) : Prop := c = some (.rw b) ∨ c = some (.ro b)

theorem own_left {h1 h2 : Heap} {a : BitVec 64} {b : BitVec 8} (h : Own (h1.phys a) b) :
    Own ((h1.union h2).phys a) b := by
  rcases h with h | h
  · exact Or.inl (cell_union_left h)
  · exact Or.inr (cell_union_left h)

theorem own_right {h1 h2 : Heap} (hd : h1.Disjoint h2) {a : BitVec 64} {b : BitVec 8}
    (h : Own (h2.phys a) b) : Own ((h1.union h2).phys a) b := by
  rcases h with h | h
  · exact Or.inl (cell_union_right_rw hd h)
  · exact Or.inr (cell_union_right_ro hd h)

theorem own_matches {h : Heap} {m : Memory} (hm : h.Matches m) {a : BitVec 64} {b : BitVec 8}
    (hc : Own (h.phys a) b) : m.read8 a = b ∧ (m.perm a).r = true ∧ m.isLazyFree a = false := by
  rcases hc with hc | hc
  · have := hm.1 a _ hc
    exact ⟨this.1, by rw [this.2.1]; rfl, this.2.2⟩
  · exact hm.1 a _ hc

theorem disj_own {h h' : Heap} (hd : h.Disjoint h') {a : BitVec 64} {b b' : BitVec 8}
    (h1 : h.phys a = some (.rw b)) (h2 : Own (h'.phys a) b') : False := by
  rcases h2 with h2 | h2
  · exact disj_rw hd h1 h2
  · exact disj_rw hd h1 h2

theorem bytesIn_cell {ro : Bool} {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap}
    (hb : (bytesIn ro a bs).holds h) (k : Nat) (hk : k < bs.length) :
    h.phys (a + BitVec.ofNat 64 k) = some (if ro then .ro bs[k] else .rw bs[k]) := by
  cases ro
  · exact bytes_rw bs a h hb k hk
  · exact bytes_ro bs a h hb k hk


end Poly1305DebianCtBlocks

end
end

end
end

section
section
/-! # One `Step` lemma per instruction shape of `poly1305_blocks`

Generated from the `r_…` reach lemmas of the functional proof (`Port.lean`): each `t_…` states the
step from `mkS s0 pc …` to its successor. The flag-setting and branch lemmas are written by hand. -/

set_option autoImplicit false

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Arm64.Obj

variable {pl : Placement} {X : String → Option (State → State)} {s0 : State}
  {pc sp : BitVec 64} {m : Memory} {ps : PState} {r : Nat → BitVec 64}

/-! ## Arithmetic and logic -/

/-- `add xd, xn, xm, lsl #a`. -/
theorem t_addLsl {d n k : BitVec 5} {a : Nat} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSL a))
    (ha : a < 64 := by decide)
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + (r k.toNat).toNat * 2 ^ a)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_addSubShift]
  simp only [execAddSubShift, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalAddSub, State.writeReg, shiftVal, shift64]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC, Bool.false_eq_true, if_false]
  refine mkS_upd_congr ?_
  simp [AddWithCarry64, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt ha]
  omega

/-- `add xd, xn, xm, lsr #a`. -/
theorem t_addLsr {d n k : BitVec 5} {a : Nat} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSR a))
    (ha : a < 64 := by decide)
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + (r k.toNat).toNat / 2 ^ a)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_addSubShift]
  simp only [execAddSubShift, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalAddSub, State.writeReg, shiftVal, shift64]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC, Bool.false_eq_true, if_false]
  refine mkS_upd_congr ?_
  have hy : (r k.toNat).toNat % 36893488147419103232 = (r k.toNat).toNat :=
    Nat.mod_eq_of_lt (by have := (r k.toNat).isLt; omega)
  simp [AddWithCarry64, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt ha, hy]
  omega

/-- `adc xd, xn, xm`. -/
theorem t_adc {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubCarry .W64 .ADD (.gpr d) (.gpr n) (.gpr k)))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + (r k.toNat).toNat + cv ps.c)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_addSubCarry]
  simp only [execAddSubCarry, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalAddSub, State.writeReg, mkS_pstate]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC, Bool.false_eq_true, if_false]
  refine mkS_upd_congr ?_
  cases ps.c <;> simp [AddWithCarry64, BitVec.toNat_add, BitVec.toNat_setWidth, cv] <;> omega

/-- `cinc xd, xn, hs` (`csinc xd, xn, xn, lo`). -/
theorem t_cinc {d n : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.condSelect .W64 .CSINC (.gpr d) (.gpr n) (.gpr n) .CC))
    (hd : Ok d := by decide) (hn : Ok n := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + cv ps.c)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_condSelect]
  simp only [execCondSelect, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, mkS_pstate, ConditionHolds]
  cases ps.c <;> simp [wr_gpr _ _ _ _ _ _ _ hd, State.writeReg, cv] <;> refine mkS_upd_congr ?_ <;>
    simp [BitVec.toNat_add]

/-- `mul xd, xn, xm` (`madd xd, xn, xm, xzr`). -/
theorem t_mul {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.dataProc3 .W64 .MADD (.gpr d) (.gpr n) (.gpr k) .xzr))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat * (r k.toNat).toNat)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_dataProc3]
  simp only [execDataProc3, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk, rd_xzr,
    State.writeReg, wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  refine mkS_upd_congr ?_
  simp [BitVec.toNat_mul]

/-- `umulh xd, xn, xm`. -/
theorem t_umulh {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.dataProc3 .W64 .UMULH (.gpr d) (.gpr n) (.gpr k) .xzr))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat * (r k.toNat).toNat / 2 ^ 64)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_dataProc3]
  simp only [execDataProc3, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    State.writeReg, wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  refine mkS_upd_congr ?_
  have hxy : (r n.toNat).toNat * (r k.toNat).toNat < 340282366920938463463374607431768211456 := by
    have := Nat.mul_lt_mul'' (r n.toNat).isLt (r k.toNat).isLt
    simpa using this
  simp [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hxy]

/-- `extr xd, xn, xm, #lsb`: bits `lsb ..< lsb + 64` of `xn:xm`. -/
theorem t_extr {d n k : BitVec 5} {lsb : Nat} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.extr .W64 (.gpr d) (.gpr n) (.gpr k) lsb))
    (hl : 0 < lsb ∧ lsb < 64 := by decide)
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r k.toNat).toNat / 2 ^ lsb + (r n.toNat).toNat * 2 ^ (64 - lsb))))) := by
  refine step_mkS hrun hf ?_
  rw [ex_extr]
  simp only [State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    State.writeReg, wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  refine mkS_upd_congr ?_
  have hk' := (r k.toNat).isLt
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl.2, Nat.shiftRight_eq_div_pow]
  rw [← Nat.shiftLeft_add_eq_or_of_lt hk', Nat.shiftLeft_eq, extr_nat _ _ _ hl.2.le]

/-- `and xd, xn, #(2^k - 1)`. -/
theorem t_andMask {d n : BitVec 5} {mask : BitVec 64} (k : Nat) (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.logicalImm .W64 .AND (.gpr d) (.gpr n) mask))
    (hm : mask = BitVec.ofNat 64 (2 ^ k - 1) := by decide) (hk : k < 64 := by decide)
    (hd : Ok d := by decide) (hn : Ok n := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat % 2 ^ k)))) := by
  subst hm
  refine step_mkS hrun hf ?_
  rw [ex_logicalImm]
  simp only [execLogicalImm, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, evalLogical,
    State.writeReg, wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  refine mkS_upd_congr ?_
  have h1 : 2 ^ k - 1 < 2 ^ 64 := by
    have := Nat.pow_lt_pow_right (show 1 < 2 by decide) hk
    omega
  have h2 := (r n.toNat).isLt
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
    Nat.and_two_pow_sub_one_eq_mod]
  have : (r n.toNat).toNat % 2 ^ k < 2 ^ 64 := lt_of_le_of_lt (Nat.mod_le _ _) h2
  rw [Nat.mod_eq_of_lt this]

/-- `lsl xd, xn, #2` (`ubfm xd, xn, #62, #61`). -/
theorem t_lsl2 {d n : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.bitfield .W64 .UBFM (.gpr d) (.gpr n) 62 61))
    (hd : Ok d := by decide) (hn : Ok n := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat * 4)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_bitfield]
  simp only [execBitfield, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, evalBitfield, State.writeReg,
    wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  simp only [Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, beq_self_eq_true, Bool.and_self, if_true,
    show (BitfieldOp.UBFM == BitfieldOp.UBFM) = true from rfl]
  simp
  refine mkS_upd_congr ?_
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-! ## Branches -/

theorem t_ret (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ret (.gpr 0x1e#5))) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (s0.readReg64 (.gpr 0x1e#5)) sp m ps r) :=
  step_mkS hrun hf (by
    rw [ex_ret, rd_hi _ _ _ _ _ _ _ (by decide)]; simp)

/-! ## Loads and stores (64-bit) -/

/-- `ldp xt1, xt2, [xb, #off]`. -/
theorem t_ldp64 {t1 t2 b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ldp .W64 false (.gpr t1) (.gpr t2) (.Offset (.gpr b) off)))
    (hb : b ≠ 31#5 := by decide)
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hr1 : m.canRead a 8 = true) (hr2 : m.canRead (a + 8#64) 8 = true)
    (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd (upd r t1.toNat (m.read64 a)) t2.toNat (m.read64 (a + 8#64)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_ldp]
  simp only [execLdp, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hr1, hr2, Bool.and_self,
    MemWidth.bytes, Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ h1,
    wr_gpr _ _ _ _ _ _ _ h2, mkS_advancePC]

/-- `ldp xt1, xt2, [xb], #16` (post-index; `b ∉ {t1, t2}`). -/
theorem t_ldpPost {t1 t2 b : BitVec 5} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ldp .W64 false (.gpr t1) (.gpr t2) (.PostIndex (.gpr b) off)))
    (hr1 : m.canRead (r b.toNat) 8 = true) (hr2 : m.canRead (r b.toNat + 8#64) 8 = true)
    (hb : Ok b := by decide) (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd (upd (upd r b.toNat (r b.toNat + off)) t1.toNat (m.read64 (r b.toNat))) t2.toNat (m.read64 (r b.toNat + 8#64)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_ldp]
  simp only [execLdp, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, rd_gpr _ _ _ _ _ _ _ hb, hr1, hr2,
    Bool.and_self, MemWidth.bytes, Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ hb,
    wr_gpr _ _ _ _ _ _ _ h1, wr_gpr _ _ _ _ _ _ _ h2, mkS_advancePC]

/-- `ldrb wt, [xb, #off]`. -/
theorem t_ldrb {t b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ldr .W32 .B8 false (.gpr t) (.Offset (.gpr b) off)))
    (hb : b ≠ 31#5 := by decide)
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hr : m.canRead a 1 = true) (ht : Ok t := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r t.toNat (BitVec.ofNat 64 (m.read8 a).toNat))) := by
  refine step_mkS hrun hf ?_
  rw [ex_ldr]
  simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hr,
    MemWidth.bytes, Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ ht, mkS_advancePC]
  refine mkS_upd_congr ?_
  simp [BitVec.toNat_setWidth]

/-- `stp xt1, xt2, [xb, #off]`. -/
theorem t_stp64 {t1 t2 b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.stp .W64 (.gpr t1) (.gpr t2) (.Offset (.gpr b) off)))
    (hb : b ≠ 31#5 := by decide)
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hw1 : m.canWrite a 8 = true) (hw2 : m.canWrite (a + 8#64) 8 = true)
    (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp ((m.write64 a (r t1.toNat)).write64 (a + 8#64) (r t2.toNat)) ps r) := by
  refine step_mkS hrun hf ?_
  rw [ex_stp]
  simp only [execStp, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hw1, hw2, Bool.and_self,
    MemWidth.bytes, Memory.writeSized, rd_gpr _ _ _ _ _ _ _ h1, rd_gpr _ _ _ _ _ _ _ h2,
    mkS_setMem, mkS_advancePC]

/-- `str xt, [xb, #off]`. -/
theorem t_str64 {t b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.str .X64 (.gpr t) (.Offset (.gpr b) off)))
    (hb : b ≠ 31#5 := by decide)
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hw : m.canWrite a 8 = true) (ht : Ok t := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp (m.write64 a (r t.toNat)) ps r) := by
  refine step_mkS hrun hf ?_
  rw [ex_str]
  simp only [execStr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hw,
    MemWidth.bytes, Memory.writeSized, rd_gpr _ _ _ _ _ _ _ ht, mkS_setMem, mkS_advancePC]

/-! ## Instructions only the GCC build uses -/

/-- `cset xd, eq` (`csinc xd, xzr, xzr, ne`). -/
theorem t_cset {d : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.condSelect .W64 .CSINC (.gpr d) .xzr .xzr .NE))
    (hd : Ok d := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps (upd r d.toNat (BitVec.ofNat 64 (if ps.z then 1 else 0)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_condSelect]
  simp only [execCondSelect, State.readReg, rd_xzr, mkS_pstate, ConditionHolds]
  by_cases hz : ps.z = true <;> simp [hz, wr_gpr _ _ _ _ _ _ _ hd, State.writeReg]


/-- `adds xd, xn, xm`. -/
theorem t_adds {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubShift .W64 .ADDS (.gpr d) (.gpr n) (.gpr k) .LSL 0))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m
      (AddWithCarry64 (r n.toNat) (r k.toNat) false).2
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + (r k.toNat).toNat)))) := by
  refine step_mkS hrun hf ?_
  rw [ex_addSubShift]
  simp only [execAddSubShift, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalAddSub, State.writeReg, shiftVal, shift64, Nat.zero_mod, BitVec.shiftLeft_zero]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_setPState, mkS_advancePC]
  refine mkS_upd_congr ?_
  simp [AddWithCarry64, BitVec.toNat_add, BitVec.toNat_setWidth]
  omega

/-- `cmp wn, #0`. -/
theorem t_cmpW0 {n : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubImm .W32 .SUBS .xzr (.gpr n) 0x000#12 false))
    (hn : Ok n := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m
      (AddWithCarry32 ((r n.toNat).setWidth 32)
        (~~~((0x000#12).setWidth 64 : BitVec 64).setWidth 32) true).2 r) := by
  refine step_mkS hrun hf ?_
  rw [ex_addSubImm]
  simp only [execAddSubImm, State.readReg, State.readReg32, rd_gpr _ _ _ _ _ _ _ hn, evalAddSub,
    State.writeReg, wr_xzr, mkS_setPState, mkS_advancePC]
  simp [BitVec.toNat_setWidth]

/-- `cmp xn, xm`. -/
theorem t_cmpReg {n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubShift .W64 .SUBS .xzr (.gpr n) (.gpr k) .LSL 0))
    (hn : Ok n := by decide) (hk : Ok k := by decide) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m
      (AddWithCarry64 (r n.toNat) (~~~(r k.toNat)) true).2 r) := by
  refine step_mkS hrun hf ?_
  rw [ex_addSubShift]
  simp only [execAddSubShift, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalAddSub, State.writeReg, shiftVal, shift64, Nat.zero_mod, BitVec.shiftLeft_zero]
  simp

theorem t_bCond_t {c : CondCode} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.bCond c off)) (hc : ConditionHolds c ps = true) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + off) sp m ps r) :=
  step_mkS hrun hf (by rw [ex_bCond]; simp [hc])

theorem t_bCond_f {c : CondCode} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.bCond c off)) (hc : ConditionHolds c ps = false) :
    Step (prog pl X) (mkS s0 pc sp m ps r) (mkS s0 (pc + 4#64) sp m ps r) :=
  step_mkS hrun hf (by rw [ex_bCond]; simp [hc])

end Poly1305DebianCtBlocks

end
end

section
section
/-! # Two runs in lock step: the rules behind every constant-time proof of this mission

`Leakage.ObsEquiv prog arity stop₁ stop₂ s₁ s₂` says the runs from `s₁` and `s₂` reveal the same
observations and stop together. It is proved backwards, one step of both runs at a time:

* `oe_stop`: both runs have stopped;
* `oe_exec`: both runs fetch the same instruction at the same `pc`, it reveals the same values in
  both (`leakedValues`), and the successors are again observationally equivalent;
* `oe_hook`: both runs enter the same hooked function with the same revealed arguments, and the
  hook's results are observationally equivalent;
* `ct_of_rel`: a lemma of the shape "for every pair of related entry states and every continuation
  that is fine on related return states, the pair is fine" gives `ct_subroutine_ok`.

Stop conditions only need to agree on states with equal `pc`, `sp` and status (`StopCompat`);
`SubroutineStop a₁`, `SubroutineStop a₂` do when `a₁`, `a₂` agree on `lr` and `sp`
(`stopCompat_sub`). Loops are plain induction over the iteration index, and a call to a function of
the library is the callee's relational lemma applied with the caller's continuation. -/

set_option autoImplicit false

namespace Poly1305DebianCtFw

open Arm64 Leakage

/-! ## Determinism of a step -/

theorem externAt_none_of_fetch {p : Program} {m : Memory} {pc : BitVec 64} {i : Instr}
    (h : p.fetchMem m pc = some i) : p.externAt? pc = none := by
  unfold Program.fetchMem at h
  cases hx : p.externAt? pc with
  | none => rfl
  | some f => simp [hx] at h

theorem fetch_none_of_extern {p : Program} {m : Memory} {pc : BitVec 64} {f : State → State}
    (h : p.externAt? pc = some f) : p.fetchMem m pc = none := by
  unfold Program.fetchMem; simp [h]

theorem step_exec_eq {p : Program} {s s' : State} {i : Instr}
    (hf : p.fetchMem s.mem s.pc = some i) (hs : Step p s s') : s' = p.evalInst i s := by
  cases hs with
  | exec _ h_fetch => rw [hf] at h_fetch; cases h_fetch; rfl
  | halt_unmapped _ h_fetch => rw [hf] at h_fetch; cases h_fetch
  | externHook _ h_ext => rw [externAt_none_of_fetch hf] at h_ext; cases h_ext
  | extern_fault _ h_ext => rw [externAt_none_of_fetch hf] at h_ext; cases h_ext

theorem step_hook_eq {p : Program} {s s' : State} {f : State → State}
    (he : p.externAt? s.pc = some f) (hk : s.mem.KeepsFrozen (f s).mem)
    (hy : (f s).symtab = s.symtab) (hs : Step p s s') : s' = f s := by
  cases hs with
  | exec _ h_fetch => rw [fetch_none_of_extern he] at h_fetch; cases h_fetch
  | halt_unmapped _ _ h_ext => rw [he] at h_ext; cases h_ext
  | externHook _ h_ext => rw [he] at h_ext; cases h_ext; rfl
  | extern_fault _ h_ext h_nkeep => rw [he] at h_ext; cases h_ext; exact absurd ⟨hk, hy⟩ h_nkeep

/-- `Step` is deterministic. -/
theorem step_det {p : Program} {s a b : State} (ha : Step p s a) (hb : Step p s b) : a = b := by
  cases ha with
  | exec _ hf => exact (step_exec_eq hf hb).symm
  | halt_unmapped hr hf hx =>
    cases hb with
    | exec _ hf' => rw [hf] at hf'; cases hf'
    | halt_unmapped => rfl
    | externHook _ hx' => rw [hx] at hx'; cases hx'
    | extern_fault _ hx' => rw [hx] at hx'; cases hx'
  | externHook _ hx hk hy => exact (step_hook_eq hx hk hy hb).symm
  | extern_fault _ hx hn =>
    cases hb with
    | exec _ hf' => rw [fetch_none_of_extern hx] at hf'; cases hf'
    | halt_unmapped _ _ hx' => rw [hx] at hx'; cases hx'
    | externHook _ hx' hk hy => rw [hx] at hx'; cases hx'; exact absurd ⟨hk, hy⟩ hn
    | extern_fault _ hx' => rw [hx] at hx'

/-! ## The observation of one step -/

theorem hookName_none {p : Program} {pc : BitVec 64} (h : p.externAt? pc = none) :
    hookName? p pc = none := by
  unfold Program.externAt? Program.hookAtOff? at h
  rw [Option.or_eq_none_iff] at h
  obtain ⟨h1, h2⟩ := h
  rw [List.findSome?_eq_none_iff] at h1 h2
  unfold hookName?
  rw [Option.or_eq_none_iff, List.findSome?_eq_none_iff, List.findSome?_eq_none_iff]
  constructor
  · rintro ⟨n, o⟩ hx
    have := h1 ⟨n, o⟩ hx
    by_cases ho : o = (pc - p.base).toNat <;> simp_all
  · rintro ⟨n, o⟩ hx
    have := h2 ⟨n, o⟩ hx
    by_cases ho : o = (pc - p.base).toNat <;> simp_all

theorem stepObs_exec {p : Program} {ar : String → Nat} {s : State} {i : Instr}
    (hf : p.fetchMem s.mem s.pc = some i) : stepObs p ar s = (s.pc, leakedValues i s) := by
  unfold stepObs
  rw [hookName_none (externAt_none_of_fetch hf), hf]

/-! ## Stop conditions -/

/-- `stop₁` and `stop₂` agree on states with equal `pc`, `sp` and status. -/
def StopCompat (stop₁ stop₂ : State → Prop) : Prop :=
  ∀ s₁ s₂ : State, s₁.pc = s₂.pc → s₁.sp = s₂.sp → s₁.status = s₂.status → (stop₁ s₁ ↔ stop₂ s₂)

theorem stopCompat_sub {a₁ a₂ : State} (hlr : a₁.readReg64 Reg.lr = a₂.readReg64 Reg.lr)
    (hsp : a₁.sp = a₂.sp) : StopCompat (SubroutineStop a₁) (SubroutineStop a₂) := by
  intro s₁ s₂ hpc hs hst
  unfold SubroutineStop Returned
  rw [hpc, hs, hst, hlr, hsp]

/-! ## Observational equivalence, backwards -/

section rules
variable {p : Program} {ar : String → Nat} {stop₁ stop₂ : State → Prop}


theorem obsUntil_stopped {s f : State} {t : List Obs} (hs : stop₁ s)
    (h : ObsUntil p ar stop₁ s t f) : t = [] ∧ f = s := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step hc _ _ => exact absurd hs hc

theorem obsIncluded_stop {s₁ s₂ : State} (h1 : stop₁ s₁) (h2 : stop₂ s₂) :
    ObsIncluded p ar stop₁ stop₂ s₁ s₂ := by
  intro t f₁ hr
  obtain ⟨rfl, rfl⟩ := obsUntil_stopped h1 hr
  exact ⟨s₂, ObsUntil.refl s₂, iff_of_true h1 h2⟩

/-- Both runs have stopped. -/
theorem oe_stop {s₁ s₂ : State} (h1 : stop₁ s₁) (h2 : stop₂ s₂) :
    ObsEquiv p ar stop₁ stop₂ s₁ s₂ :=
  ⟨obsIncluded_stop h1 h2, obsIncluded_stop h2 h1⟩

/-- One step of the simulation: the stops agree, the observations agree, and each step of the
first run is matched by a step of the second to states again included. -/
theorem obsIncluded_of_step {s₁ s₂ : State} (hstop : stop₁ s₁ ↔ stop₂ s₂)
    (hobs : stepObs p ar s₁ = stepObs p ar s₂)
    (hstep : ∀ s₁', Step p s₁ s₁' → ∃ s₂', Step p s₂ s₂' ∧ ObsIncluded p ar stop₁ stop₂ s₁' s₂') :
    ObsIncluded p ar stop₁ stop₂ s₁ s₂ := by
  intro t f₁ hr
  cases hr with
  | refl => exact ⟨s₂, ObsUntil.refl s₂, hstop⟩
  | @step _ s₁' _ t' hc hs hrest =>
    obtain ⟨s₂', hs₂, hinc⟩ := hstep s₁' hs
    obtain ⟨f₂, hr₂, hiff⟩ := hinc t' f₁ hrest
    refine ⟨f₂, ?_, hiff⟩
    rw [hobs]
    exact ObsUntil.step (fun h => hc (hstop.mpr h)) hs₂ hr₂

/-- One step of each run, given as `Step` facts, with equal observations. -/
theorem oe_step (hc : StopCompat stop₁ stop₂) {s₁ s₂ t₁ t₂ : State}
    (hpc : s₁.pc = s₂.pc) (hsp : s₁.sp = s₂.sp) (hst : s₁.status = s₂.status)
    (h1 : Step p s₁ t₁) (h2 : Step p s₂ t₂)
    (hobs : stepObs p ar s₁ = stepObs p ar s₂)
    (h : ObsEquiv p ar stop₁ stop₂ t₁ t₂) : ObsEquiv p ar stop₁ stop₂ s₁ s₂ := by
  have hstop := hc s₁ s₂ hpc hsp hst
  refine ⟨obsIncluded_of_step hstop hobs ?_, obsIncluded_of_step hstop.symm hobs.symm ?_⟩
  · intro s₁' hs
    rw [step_det hs h1]
    exact ⟨_, h2, h.1⟩
  · intro s₂' hs
    rw [step_det hs h2]
    exact ⟨_, h1, h.2⟩

theorem oe_congr {s₁ s₂ t₁ t₂ : State} (e1 : s₁ = t₁) (e2 : s₂ = t₂)
    (h : ObsEquiv p ar stop₁ stop₂ t₁ t₂) : ObsEquiv p ar stop₁ stop₂ s₁ s₂ := by
  subst e1 e2; exact h

end rules

/-! ## Observation sequences compose -/

/-! ## From a relational lemma to `ct_subroutine_ok` -/

/-- Two states that differ at most in memory: the second is the first with its memory. -/
theorem sameExceptMem_eq {s₁ s₂ : State} (h : SameExceptMem s₁ s₂) :
    s₂ = { s₁ with mem := s₂.mem } := by
  cases s₁; cases s₂; unfold SameExceptMem at h; simp only [State.mk.injEq] at h ⊢
  simp_all

end Poly1305DebianCtFw

end
end

section
section
/-! # Two runs of `poly1305_blocks` in lock step

The relational lemma `blocks_rel` is stated in continuation-passing form so that callers
(`poly1305_update`, `poly1305_finish`) use it at their `bl poly1305_blocks`: the two runs enter with
equal `x0`, `x1`, `x2`, `lr`, `sp`, equal `final` byte, and anything in `x3..x17`; they return to
`lr` with `sp` unchanged, all registers outside `x1..x17` as at entry, and memory changed only in
the accumulator bytes (`MemOk`). The loop reveals the message addresses `x1 + 16 k` and the state
addresses `x0 + 0, 8, …, 40, 88`; it branches only on `x1 = x2`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtBlocks

open Arm64 Arm64.Obj Poly1305DebianCt Leakage Poly1305DebianCtFw

theorem pc4 (b : BitVec 64) (x y : Nat) (h : x + 4 = y := by decide) :
    b + BitVec.ofNat 64 x + 4#64 = b + BitVec.ofNat 64 y := by
  rw [pc_add, h]

theorem rd_x0 (s0 : State) (pc sp : BitVec 64) (m : Memory) (ps : PState) (r : Nat → BitVec 64) :
    (mkS s0 pc sp m ps r).readReg64 (.gpr 0#5) = X0 s0 := rfl

/-- What the precondition gives about a run's entry state (no values). -/
structure CtFacts (pl : Placement) (X : String → Option (State → State)) (s0 : State) : Prop where
  good : Good pl X s0 s0.mem
  rs : ∀ k < 24, ¬ W s0 (X0 s0 + BitVec.ofNat 64 k) ∧
    (s0.mem.perm (X0 s0 + BitVec.ofNat 64 k)).r = true ∧
    s0.mem.isLazyFree (X0 s0 + BitVec.ofNat 64 k) = false
  fn : ¬ W s0 (X0 s0 + BitVec.ofNat 64 88) ∧ (s0.mem.perm (X0 s0 + BitVec.ofNat 64 88)).r = true ∧
    s0.mem.isLazyFree (X0 s0 + BitVec.ofNat 64 88) = false

theorem rs_canRead' {pl : Placement} {X : String → Option (State → State)} {s0 : State} {m : Memory}
    (F : CtFacts pl X s0) (hm : MemOk s0 m) (off : Nat) (h : off + 8 ≤ 24) :
    m.canRead (X0 s0 + BitVec.ofNat 64 off) 8 = true :=
  canRead_notW hm fun k hk => by rw [pc_add]; exact F.rs (off + k) (by omega)

theorem fin_canRead' {pl : Placement} {X : String → Option (State → State)} {s0 : State} {m : Memory}
    (F : CtFacts pl X s0) (hm : MemOk s0 m) :
    m.canRead (X0 s0 + BitVec.ofNat 64 88) 1 = true :=
  canRead_notW hm fun k hk => by
    have : k = 0 := by omega
    subst this; simpa using F.fn

theorem cmpReg_z (a b : BitVec 64) : (AddWithCarry64 a (~~~b) true).2.z = decide (a = b) := by
  simp only [AddWithCarry64]
  rw [Bool.eq_iff_iff]; simp; bv_omega

section rel

variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

/-- One instruction in both runs, as `Step` facts of the abstract states `mkS`. -/
theorem rb (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State} (hst : c₁.status = c₂.status)
    {pc sp₁ sp₂ : BitVec 64} (hsp : sp₁ = sp₂) {m₁ m₂ : Memory} {ps₁ ps₂ : PState}
    {r₁ r₂ : Nat → BitVec 64} {i : Instr} {t₁ t₂ : State}
    (hf1 : (prog pl X).fetchMem m₁ pc = some i) (hf2 : (prog pl X).fetchMem m₂ pc = some i)
    (st1 : Step (prog pl X) (mkS c₁ pc sp₁ m₁ ps₁ r₁) t₁)
    (st2 : Step (prog pl X) (mkS c₂ pc sp₂ m₂ ps₂ r₂) t₂)
    (hl : leakedValues i (mkS c₁ pc sp₁ m₁ ps₁ r₁) = leakedValues i (mkS c₂ pc sp₂ m₂ ps₂ r₂))
    (h : ObsEquiv (prog pl X) arity stop₁ stop₂ t₁ t₂) :
    ObsEquiv (prog pl X) arity stop₁ stop₂ (mkS c₁ pc sp₁ m₁ ps₁ r₁) (mkS c₂ pc sp₂ m₂ ps₂ r₂) := by
  refine oe_step hc rfl hsp hst st1 st2 ?_ h
  rw [stepObs_exec (s := mkS c₁ pc sp₁ m₁ ps₁ r₁) hf1,
    stepObs_exec (s := mkS c₂ pc sp₂ m₂ ps₂ r₂) hf2, hl]
  rfl

/-- An instruction of the block loop's body in both runs: only `x1` and `x2` are tracked. -/
theorem rbody (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State} (hst : c₁.status = c₂.status)
    {pc sp₁ sp₂ : BitVec 64} (hsp : sp₁ = sp₂) {m₁ m₂ : Memory} {ps₁ ps₂ ps₁' ps₂' : PState}
    {r₁ r₂ r₁' r₂' : Nat → BitVec 64} {i : Instr} {P Q : BitVec 64}
    (hf1 : (prog pl X).fetchMem m₁ pc = some i) (hf2 : (prog pl X).fetchMem m₂ pc = some i)
    (st1 : Step (prog pl X) (mkS c₁ pc sp₁ m₁ ps₁ r₁) (mkS c₁ (pc + 4#64) sp₁ m₁ ps₁' r₁'))
    (st2 : Step (prog pl X) (mkS c₂ pc sp₂ m₂ ps₂ r₂) (mkS c₂ (pc + 4#64) sp₂ m₂ ps₂' r₂'))
    (hl : leakedValues i (mkS c₁ pc sp₁ m₁ ps₁ r₁) = leakedValues i (mkS c₂ pc sp₂ m₂ ps₂ r₂))
    (e1 : r₁' 1 = P) (e2 : r₂' 1 = P) (e3 : r₁' 2 = Q) (e4 : r₂' 2 = Q)
    (h : ∀ (ρ₁ ρ₂ : PState) (q₁ q₂ : Nat → BitVec 64), q₁ 1 = P → q₂ 1 = P → q₁ 2 = Q → q₂ 2 = Q →
      ObsEquiv (prog pl X) arity stop₁ stop₂ (mkS c₁ (pc + 4#64) sp₁ m₁ ρ₁ q₁)
        (mkS c₂ (pc + 4#64) sp₂ m₂ ρ₂ q₂)) :
    ObsEquiv (prog pl X) arity stop₁ stop₂ (mkS c₁ pc sp₁ m₁ ps₁ r₁) (mkS c₂ pc sp₂ m₂ ps₂ r₂) :=
  rb hc hst hsp hf1 hf2 st1 st2 hl (h _ _ _ _ e1 e2 e3 e4)

end rel

section body

variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

set_option maxHeartbeats 4000000 in
/-- One iteration of the block loop's body (offsets 0x2c..0xf8), in both runs. -/
theorem body2 (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State} (hst : c₁.status = c₂.status)
    (hrun₁ : c₁.status = .Running) (hrun₂ : c₂.status = .Running)
    {m₁ m₂ : Memory} (hg₁ : Good pl X c₁ m₁) (hg₂ : Good pl X c₂ m₂)
    {sp₁ sp₂ : BitVec 64} (hsp : sp₁ = sp₂) {ps₁ ps₂ : PState} {r₁ r₂ : Nat → BitVec 64}
    {P Q : BitVec 64} (e1₁ : r₁ 1 = P) (e1₂ : r₂ 1 = P) (e2₁ : r₁ 2 = Q) (e2₂ : r₂ 2 = Q)
    (hr1₁ : m₁.canRead P 8 = true) (hr2₁ : m₁.canRead (P + 8#64) 8 = true)
    (hr1₂ : m₂.canRead P 8 = true) (hr2₂ : m₂.canRead (P + 8#64) 8 = true)
    (k : ∀ (ρ₁ ρ₂ : PState) (q₁ q₂ : Nat → BitVec 64), q₁ 1 = P + 16#64 → q₂ 1 = P + 16#64 →
      q₁ 2 = Q → q₂ 2 = Q →
      ObsEquiv (prog pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 668#64) sp₁ m₁ ρ₁ q₁)
        (mkS c₂ (pl.base + 668#64) sp₂ m₂ ρ₂ q₂)) :
    ObsEquiv (prog pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 460#64) sp₁ m₁ ps₁ r₁)
      (mkS c₂ (pl.base + 460#64) sp₂ m₂ ps₂ r₂) := by
  have b1 : (0x01#5 : BitVec 5).toNat = 1 := rfl
  -- ldp x4, x5, [x1], #16
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_2c hg₁) (f_2c hg₂)
    (t_ldpPost hrun₁ (f_2c hg₁) (by rw [b1, e1₁]; exact hr1₁) (by rw [b1, e1₁]; exact hr2₁))
    (t_ldpPost hrun₂ (f_2c hg₂) (by rw [b1, e1₂]; exact hr1₂) (by rw [b1, e1₂]; exact hr2₂))
    (by simp [leakedValues, evalAddrMode, rd_gpr _ _ _ _ _ _ _ (show Ok 1#5 by decide), e1₁, e1₂])
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 460 464]
  -- andMask at 464
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_30 hg₁) (f_30 hg₂) (t_andMask 44 hrun₁ (f_30 hg₁)) (t_andMask 44 hrun₂ (f_30 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 464 468]
  -- extr at 468
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_34 hg₁) (f_34 hg₂) (t_extr hrun₁ (f_34 hg₁)) (t_extr hrun₂ (f_34 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 468 472]
  -- andMask at 472
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_38 hg₁) (f_38 hg₂) (t_andMask 44 hrun₁ (f_38 hg₁)) (t_andMask 44 hrun₂ (f_38 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 472 476]
  -- extr at 476
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_3c hg₁) (f_3c hg₂) (t_extr hrun₁ (f_3c hg₁)) (t_extr hrun₂ (f_3c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 476 480]
  -- addLsl at 480
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_40 hg₁) (f_40 hg₂) (t_addLsl hrun₁ (f_40 hg₁)) (t_addLsl hrun₂ (f_40 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 480 484]
  -- addLsl at 484
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_44 hg₁) (f_44 hg₂) (t_addLsl hrun₁ (f_44 hg₁)) (t_addLsl hrun₂ (f_44 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 484 488]
  -- addLsl at 488
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_48 hg₁) (f_48 hg₂) (t_addLsl hrun₁ (f_48 hg₁)) (t_addLsl hrun₂ (f_48 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 488 492]
  -- mul at 492
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_4c hg₁) (f_4c hg₂) (t_mul hrun₁ (f_4c hg₁)) (t_mul hrun₂ (f_4c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 492 496]
  -- mul at 496
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_50 hg₁) (f_50 hg₂) (t_mul hrun₁ (f_50 hg₁)) (t_mul hrun₂ (f_50 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 496 500]
  -- umulh at 500
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_54 hg₁) (f_54 hg₂) (t_umulh hrun₁ (f_54 hg₁)) (t_umulh hrun₂ (f_54 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 500 504]
  -- mul at 504
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_58 hg₁) (f_58 hg₂) (t_mul hrun₁ (f_58 hg₁)) (t_mul hrun₂ (f_58 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 504 508]
  -- adds at 508
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_5c hg₁) (f_5c hg₂) (t_adds hrun₁ (f_5c hg₁)) (t_adds hrun₂ (f_5c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 508 512]
  -- umulh at 512
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_60 hg₁) (f_60 hg₂) (t_umulh hrun₁ (f_60 hg₁)) (t_umulh hrun₂ (f_60 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 512 516]
  -- umulh at 516
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_64 hg₁) (f_64 hg₂) (t_umulh hrun₁ (f_64 hg₁)) (t_umulh hrun₂ (f_64 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 516 520]
  -- adc at 520
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_68 hg₁) (f_68 hg₂) (t_adc hrun₁ (f_68 hg₁)) (t_adc hrun₂ (f_68 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 520 524]
  -- adds at 524
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_6c hg₁) (f_6c hg₂) (t_adds hrun₁ (f_6c hg₁)) (t_adds hrun₂ (f_6c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 524 528]
  -- mul at 528
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_70 hg₁) (f_70 hg₂) (t_mul hrun₁ (f_70 hg₁)) (t_mul hrun₂ (f_70 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 528 532]
  -- adc at 532
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_74 hg₁) (f_74 hg₂) (t_adc hrun₁ (f_74 hg₁)) (t_adc hrun₂ (f_74 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 532 536]
  -- mul at 536
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_78 hg₁) (f_78 hg₂) (t_mul hrun₁ (f_78 hg₁)) (t_mul hrun₂ (f_78 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 536 540]
  -- umulh at 540
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_7c hg₁) (f_7c hg₂) (t_umulh hrun₁ (f_7c hg₁)) (t_umulh hrun₂ (f_7c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 540 544]
  -- extr at 544
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_80 hg₁) (f_80 hg₂) (t_extr hrun₁ (f_80 hg₁)) (t_extr hrun₂ (f_80 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 544 548]
  -- umulh at 548
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_84 hg₁) (f_84 hg₂) (t_umulh hrun₁ (f_84 hg₁)) (t_umulh hrun₂ (f_84 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 548 552]
  -- adds at 552
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_88 hg₁) (f_88 hg₂) (t_adds hrun₁ (f_88 hg₁)) (t_adds hrun₂ (f_88 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 552 556]
  -- mul at 556
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_8c hg₁) (f_8c hg₂) (t_mul hrun₁ (f_8c hg₁)) (t_mul hrun₂ (f_8c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 556 560]
  -- adc at 560
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_90 hg₁) (f_90 hg₂) (t_adc hrun₁ (f_90 hg₁)) (t_adc hrun₂ (f_90 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 560 564]
  -- mul at 564
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_94 hg₁) (f_94 hg₂) (t_mul hrun₁ (f_94 hg₁)) (t_mul hrun₂ (f_94 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 564 568]
  -- umulh at 568
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_98 hg₁) (f_98 hg₂) (t_umulh hrun₁ (f_98 hg₁)) (t_umulh hrun₂ (f_98 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 568 572]
  -- umulh at 572
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_9c hg₁) (f_9c hg₂) (t_umulh hrun₁ (f_9c hg₁)) (t_umulh hrun₂ (f_9c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 572 576]
  -- adds at 576
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_a0 hg₁) (f_a0 hg₂) (t_adds hrun₁ (f_a0 hg₁)) (t_adds hrun₂ (f_a0 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 576 580]
  -- andMask at 580
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_a4 hg₁) (f_a4 hg₂) (t_andMask 44 hrun₁ (f_a4 hg₁)) (t_andMask 44 hrun₂ (f_a4 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 580 584]
  -- mul at 584
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_a8 hg₁) (f_a8 hg₂) (t_mul hrun₁ (f_a8 hg₁)) (t_mul hrun₂ (f_a8 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 584 588]
  -- adc at 588
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_ac hg₁) (f_ac hg₂) (t_adc hrun₁ (f_ac hg₁)) (t_adc hrun₂ (f_ac hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 588 592]
  -- umulh at 592
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_b0 hg₁) (f_b0 hg₂) (t_umulh hrun₁ (f_b0 hg₁)) (t_umulh hrun₂ (f_b0 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 592 596]
  -- adds at 596
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_b4 hg₁) (f_b4 hg₂) (t_adds hrun₁ (f_b4 hg₁)) (t_adds hrun₂ (f_b4 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 596 600]
  -- cinc at 600
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_b8 hg₁) (f_b8 hg₂) (t_cinc hrun₁ (f_b8 hg₁)) (t_cinc hrun₂ (f_b8 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 600 604]
  -- adds at 604
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_bc hg₁) (f_bc hg₂) (t_adds hrun₁ (f_bc hg₁)) (t_adds hrun₂ (f_bc hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 604 608]
  -- adc at 608
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_c0 hg₁) (f_c0 hg₂) (t_adc hrun₁ (f_c0 hg₁)) (t_adc hrun₂ (f_c0 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 608 612]
  -- andMask at 612
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_c4 hg₁) (f_c4 hg₂) (t_andMask 44 hrun₁ (f_c4 hg₁)) (t_andMask 44 hrun₂ (f_c4 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 612 616]
  -- extr at 616
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_c8 hg₁) (f_c8 hg₂) (t_extr hrun₁ (f_c8 hg₁)) (t_extr hrun₂ (f_c8 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 616 620]
  -- mul at 620
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_cc hg₁) (f_cc hg₂) (t_mul hrun₁ (f_cc hg₁)) (t_mul hrun₂ (f_cc hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 620 624]
  -- umulh at 624
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_d0 hg₁) (f_d0 hg₂) (t_umulh hrun₁ (f_d0 hg₁)) (t_umulh hrun₂ (f_d0 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 624 628]
  -- adds at 628
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_d4 hg₁) (f_d4 hg₂) (t_adds hrun₁ (f_d4 hg₁)) (t_adds hrun₂ (f_d4 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 628 632]
  -- cinc at 632
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_d8 hg₁) (f_d8 hg₂) (t_cinc hrun₁ (f_d8 hg₁)) (t_cinc hrun₂ (f_d8 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 632 636]
  -- adds at 636
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_dc hg₁) (f_dc hg₂) (t_adds hrun₁ (f_dc hg₁)) (t_adds hrun₂ (f_dc hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 636 640]
  -- adc at 640
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_e0 hg₁) (f_e0 hg₂) (t_adc hrun₁ (f_e0 hg₁)) (t_adc hrun₂ (f_e0 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 640 644]
  -- andMask at 644
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_e4 hg₁) (f_e4 hg₂) (t_andMask 42 hrun₁ (f_e4 hg₁)) (t_andMask 42 hrun₂ (f_e4 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 644 648]
  -- extr at 648
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_e8 hg₁) (f_e8 hg₂) (t_extr hrun₁ (f_e8 hg₁)) (t_extr hrun₂ (f_e8 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 648 652]
  -- addLsl at 652
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_ec hg₁) (f_ec hg₂) (t_addLsl hrun₁ (f_ec hg₁)) (t_addLsl hrun₂ (f_ec hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 652 656]
  -- addLsl at 656
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_f0 hg₁) (f_f0 hg₂) (t_addLsl hrun₁ (f_f0 hg₁)) (t_addLsl hrun₂ (f_f0 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 656 660]
  -- andMask at 660
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_f4 hg₁) (f_f4 hg₂) (t_andMask 44 hrun₁ (f_f4 hg₁)) (t_andMask 44 hrun₂ (f_f4 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 660 664]
  -- addLsr at 664
  refine rbody (P := P + 16#64) (Q := Q) hc hst hsp (f_f8 hg₁) (f_f8 hg₂) (t_addLsr hrun₁ (f_f8 hg₁)) (t_addLsr hrun₂ (f_f8 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 664 668]
  exact k _ _ _ _ e1₁ e1₂ e2₁ e2₂

end body

section loop

variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

set_option maxHeartbeats 4000000 in
/-- The block loop from its head (0x2c) in both runs, then the epilogue and the return. -/
theorem loop2 (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State} (hst : c₁.status = c₂.status)
    (hrun₁ : c₁.status = .Running) (hrun₂ : c₂.status = .Running)
    (F₁ : CtFacts pl X c₁) (F₂ : CtFacts pl X c₂) (hsp : c₁.sp = c₂.sp) (hX0 : X0 c₁ = X0 c₂)
    (K : ∀ (m₁ m₂ : Memory) (ps₁ ps₂ : PState) (r₁ r₂ : Nat → BitVec 64), MemOk c₁ m₁ → MemOk c₂ m₂ →
      ObsEquiv (prog pl X) arity stop₁ stop₂
        (mkS c₁ (c₁.readReg64 (.gpr 0x1e#5)) c₁.sp m₁ ps₁ r₁)
        (mkS c₂ (c₂.readReg64 (.gpr 0x1e#5)) c₂.sp m₂ ps₂ r₂)) :
    ∀ d (n : Nat) (X1 : BitVec 64) (r₁ r₂ : Nat → BitVec 64) (ps₁ ps₂ : PState),
      n ≤ d → 16 ≤ n → n % 16 = 0 → n < 2 ^ 64 → MsgOk c₁ X1 n → MsgOk c₂ X1 n →
      r₁ 1 = X1 → r₂ 1 = X1 → r₁ 2 = X1 + BitVec.ofNat 64 n → r₂ 2 = X1 + BitVec.ofNat 64 n →
      ObsEquiv (prog pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 460#64) c₁.sp c₁.mem ps₁ r₁)
        (mkS c₂ (pl.base + 460#64) c₂.sp c₂.mem ps₂ r₂) := by
  intro d
  induction d with
  | zero => intro n _ _ _ _ _ hl h16; omega
  | succ d ih =>
    intro n X1 r₁ r₂ ps₁ ps₂ hl h16 h16d h64 hmsg₁ hmsg₂ e1₁ e1₂ e2₁ e2₂
    have hg₁ := F₁.good
    have hg₂ := F₂.good
    have hcr₁ : ∀ o, o + 8 ≤ 16 → c₁.mem.canRead (X1 + BitVec.ofNat 64 o) 8 = true := fun o ho =>
      canRead_notW hg₁.2.2 fun k hk => by rw [pc_add]; exact hmsg₁ _ (by omega)
    have hcr₂ : ∀ o, o + 8 ≤ 16 → c₂.mem.canRead (X1 + BitVec.ofNat 64 o) 8 = true := fun o ho =>
      canRead_notW hg₂.2.2 fun k hk => by rw [pc_add]; exact hmsg₂ _ (by omega)
    refine body2 hc hst hrun₁ hrun₂ hg₁ hg₂ hsp e1₁ e1₂ e2₁ e2₂ (by simpa using hcr₁ 0 (by decide))
      (hcr₁ 8 (by decide)) (by simpa using hcr₂ 0 (by decide)) (hcr₂ 8 (by decide)) ?_
    intro ρ₁ ρ₂ q₁ q₂ f1₁ f1₂ f2₁ f2₂
    have b1 : (0x01#5 : BitVec 5).toNat = 1 := rfl
    have b2 : (0x02#5 : BitVec 5).toNat = 2 := rfl
    -- cmp x1, x2
    refine rb hc hst hsp (f_fc hg₁) (f_fc hg₂) (t_cmpReg hrun₁ (f_fc hg₁)) (t_cmpReg hrun₂ (f_fc hg₂))
      rfl ?_
    rw [pc4 pl.base 668 672]
    simp only [b1, b2, f1₁, f1₂, f2₁, f2₂]
    have hz := cmpReg_z (X1 + 16#64) (X1 + BitVec.ofNat 64 n)
    have hz' : (AddWithCarry64 (X1 + 16#64) (~~~(X1 + BitVec.ofNat 64 n)) true).2.z =
        decide (16 = n) := by
      rw [hz, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl]
      exact Bool.decide_congr (add_ofNat_inj X1 (by decide) h64)
    by_cases hmore : 16 ≤ n - 16
    · have hcnd : ConditionHolds .NE (AddWithCarry64 (X1 + 16#64) (~~~(X1 + BitVec.ofNat 64 n)) true).2
          = true := by simp only [ConditionHolds, hz']; simp; omega
      refine rb hc hst hsp (f_100 hg₁) (f_100 hg₂) (t_bCond_t hrun₁ (f_100 hg₁) hcnd)
        (t_bCond_t hrun₂ (f_100 hg₂) hcnd) rfl ?_
      rw [show pl.base + 672#64 + 0xffffffffffffff2c#64 = pl.base + 460#64 by
        rw [BitVec.add_assoc]; rfl]
      have hn' : X1 + BitVec.ofNat 64 n = (X1 + 16#64) + BitVec.ofNat 64 (n - 16) := by
        rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, pc_add]; congr 2; omega
      refine ih (n - 16) (X1 + 16#64) q₁ q₂ _ _ (by omega) hmore (by omega) (by omega) ?_ ?_ f1₁ f1₂
        (by rw [f2₁, hn']) (by rw [f2₂, hn'])
      · intro j hj
        rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, pc_add]
        exact hmsg₁ _ (by omega)
      · intro j hj
        rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, pc_add]
        exact hmsg₂ _ (by omega)
    · have hcnd : ConditionHolds .NE (AddWithCarry64 (X1 + 16#64) (~~~(X1 + BitVec.ofNat 64 n)) true).2
          = false := by simp only [ConditionHolds, hz']; simp; omega
      refine rb hc hst hsp (f_100 hg₁) (f_100 hg₂) (t_bCond_f hrun₁ (f_100 hg₁) hcnd)
        (t_bCond_f hrun₂ (f_100 hg₂) hcnd) rfl ?_
      rw [pc4 pl.base 672 676]
      -- stp x7, x3, [x0, #0x18]
      refine rb hc hst hsp (f_104 hg₁) (f_104 hg₂)
        (t_stp64 hrun₁ (f_104 hg₁) (a := X0 c₁ + BitVec.ofNat 64 24) (ha := by rw [rd_x0]) (hw1 := h_canWrite hg₁.2.2 24 (by decide) (by decide)) (hw2 := by rw [add8]; exact h_canWrite hg₁.2.2 32 (by decide) (by decide)))
        (t_stp64 hrun₂ (f_104 hg₂) (a := X0 c₂ + BitVec.ofNat 64 24) (ha := by rw [rd_x0]) (hw1 := h_canWrite hg₂.2.2 24 (by decide) (by decide)) (hw2 := by rw [add8]; exact h_canWrite hg₂.2.2 32 (by decide) (by decide)))
        (by simp [leakedValues, evalAddrMode, rd_x0, hX0]) ?_
      rw [pc4 pl.base 676 680]
      simp only [add8]
      have hg2₁ := good_h (good_h hg₁ 24 (by decide) (by decide) (q₁ (0x07#5).toNat)) (24 + 8)
        (by decide) (by decide) (q₁ (0x03#5).toNat)
      have hg2₂ := good_h (good_h hg₂ 24 (by decide) (by decide) (q₂ (0x07#5).toNat)) (24 + 8)
        (by decide) (by decide) (q₂ (0x03#5).toNat)
      -- str x15, [x0, #0x28]
      refine rb hc hst hsp (f_108 hg2₁) (f_108 hg2₂)
        (t_str64 hrun₁ (f_108 hg2₁) (a := X0 c₁ + BitVec.ofNat 64 40) (ha := by rw [rd_x0]) (hw := h_canWrite hg2₁.2.2 40 (by decide) (by decide)))
        (t_str64 hrun₂ (f_108 hg2₂) (a := X0 c₂ + BitVec.ofNat 64 40) (ha := by rw [rd_x0]) (hw := h_canWrite hg2₂.2.2 40 (by decide) (by decide)))
        (by simp [leakedValues, evalAddrMode, rd_x0, hX0]) ?_
      rw [pc4 pl.base 680 684]
      have hg3₁ := good_h hg2₁ 40 (by decide) (by decide) (q₁ (0x0f#5).toNat)
      have hg3₂ := good_h hg2₂ 40 (by decide) (by decide) (q₂ (0x0f#5).toNat)
      -- ret
      refine rb hc hst hsp (f_10c hg3₁) (f_10c hg3₂) (t_ret hrun₁ (f_10c hg3₁))
        (t_ret hrun₂ (f_10c hg3₂)) rfl ?_
      exact K _ _ _ _ _ _ hg3₁.2.2 hg3₂.2.2

end loop

section top

variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

set_option maxHeartbeats 4000000 in
/-- `poly1305_blocks` in both runs, in continuation-passing form: entered at its address with equal
`x0`, `x1`, `x2`, `lr`, `sp` (`x3..x17` and the flags arbitrary), a nonzero multiple of 16 bytes
of message readable at `x1` outside the accumulator, both runs return to `lr` with `sp` unchanged,
registers outside `x1..x17` as at entry (`mkS`), and memory changed only in the accumulator
(`MemOk`). -/
theorem blocks_rel (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State}
    (hrun₁ : c₁.status = .Running) (hrun₂ : c₂.status = .Running)
    (hpc₁ : c₁.pc = pl.base + 416#64) (hpc₂ : c₂.pc = pl.base + 416#64)
    (F₁ : CtFacts pl X c₁) (F₂ : CtFacts pl X c₂) (hsp : c₁.sp = c₂.sp) (hX0 : X0 c₁ = X0 c₂)
    (hx1 : c₁.readReg64 (.gpr 1#5) = c₂.readReg64 (.gpr 1#5))
    (hx2 : c₁.readReg64 (.gpr 2#5) = c₂.readReg64 (.gpr 2#5))
    (h16 : 16 ≤ (c₁.readReg64 (.gpr 2#5)).toNat) (h16d : (c₁.readReg64 (.gpr 2#5)).toNat % 16 = 0)
    (hmsg₁ : MsgOk c₁ (c₁.readReg64 (.gpr 1#5)) (c₁.readReg64 (.gpr 2#5)).toNat)
    (hmsg₂ : MsgOk c₂ (c₁.readReg64 (.gpr 1#5)) (c₁.readReg64 (.gpr 2#5)).toNat)
    (K : ∀ (m₁ m₂ : Memory) (ps₁ ps₂ : PState) (r₁ r₂ : Nat → BitVec 64), MemOk c₁ m₁ → MemOk c₂ m₂ →
      ObsEquiv (prog pl X) arity stop₁ stop₂
        (mkS c₁ (c₁.readReg64 (.gpr 0x1e#5)) c₁.sp m₁ ps₁ r₁)
        (mkS c₂ (c₂.readReg64 (.gpr 0x1e#5)) c₂.sp m₂ ps₂ r₂)) :
    ObsEquiv (prog pl X) arity stop₁ stop₂ c₁ c₂ := by
  have hst : c₁.status = c₂.status := hrun₁.trans hrun₂.symm
  have hg₁ := F₁.good
  have hg₂ := F₂.good
  refine oe_congr (mkS_self c₁).symm (mkS_self c₂).symm ?_
  rw [hpc₁, hpc₂]
  set P := c₁.readReg64 (.gpr 1#5) with hP
  set Q := c₁.readReg64 (.gpr 2#5) with hQ
  have e1₁ : r0 c₁ 1 = P := r0_eq c₁ 1
  have e1₂ : r0 c₂ 1 = P := (r0_eq c₂ 1).trans hx1.symm
  have e2₁ : r0 c₁ 2 = Q := r0_eq c₁ 2
  have e2₂ : r0 c₂ 2 = Q := (r0_eq c₂ 2).trans hx2.symm
  generalize r0 c₁ = r₁ at e1₁ e2₁ ⊢
  generalize r0 c₂ = r₂ at e1₂ e2₂ ⊢
  generalize c₁.pstate = ps₁
  generalize c₂.pstate = ps₂
  -- ldp x12, x7, [x0, #0x10]
  refine rbody (P := P) (Q := Q) hc hst hsp (f_0 hg₁) (f_0 hg₂)
    (t_ldp64 hrun₁ (f_0 hg₁) (a := X0 c₁ + BitVec.ofNat 64 16) (ha := by rw [rd_x0])
      (hr1 := rs_canRead' F₁ hg₁.2.2 16 (by decide))
      (hr2 := by rw [add8]; exact h_canRead hg₁.2.2 24 (by decide) (by decide)))
    (t_ldp64 hrun₂ (f_0 hg₂) (a := X0 c₂ + BitVec.ofNat 64 16) (ha := by rw [rd_x0])
      (hr1 := rs_canRead' F₂ hg₂.2.2 16 (by decide))
      (hr2 := by rw [add8]; exact h_canRead hg₂.2.2 24 (by decide) (by decide)))
    (by simp [leakedValues, evalAddrMode, rd_x0, hX0])
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 416 420]
  -- add x2, x1, x2
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_4 hg₁) (f_4 hg₂)
    (t_addLsl hrun₁ (f_4 hg₁)) (t_addLsl hrun₂ (f_4 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e1₁, e2₁]) (by simp [upd, e1₂, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 420 424]
  -- ldp x8, x9, [x0]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_8 hg₁) (f_8 hg₂)
    (t_ldp64 hrun₁ (f_8 hg₁) (a := X0 c₁ + BitVec.ofNat 64 0) (ha := by rw [rd_x0])
      (hr1 := rs_canRead' F₁ hg₁.2.2 0 (by decide))
      (hr2 := by rw [add8]; exact rs_canRead' F₁ hg₁.2.2 8 (by decide)))
    (t_ldp64 hrun₂ (f_8 hg₂) (a := X0 c₂ + BitVec.ofNat 64 0) (ha := by rw [rd_x0])
      (hr1 := rs_canRead' F₂ hg₂.2.2 0 (by decide))
      (hr2 := by rw [add8]; exact rs_canRead' F₂ hg₂.2.2 8 (by decide)))
    (by simp [leakedValues, evalAddrMode, rd_x0, hX0])
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 424 428]
  -- ldrb w3, [x0, #0x58]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_c hg₁) (f_c hg₂)
    (t_ldrb hrun₁ (f_c hg₁) (a := X0 c₁ + BitVec.ofNat 64 88) (ha := by rw [rd_x0])
      (hr := fin_canRead' F₁ hg₁.2.2))
    (t_ldrb hrun₂ (f_c hg₂) (a := X0 c₂ + BitVec.ofNat 64 88) (ha := by rw [rd_x0])
      (hr := fin_canRead' F₂ hg₂.2.2))
    (by simp [leakedValues, evalAddrMode, rd_x0, hX0])
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 428 432]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_10 hg₁) (f_10 hg₂)
    (t_cmpW0 hrun₁ (f_10 hg₁)) (t_cmpW0 hrun₂ (f_10 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 432 436]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_14 hg₁) (f_14 hg₂)
    (t_addLsl hrun₁ (f_14 hg₁)) (t_addLsl hrun₂ (f_14 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 436 440]
  -- ldp x3, x15, [x0, #0x20]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_18 hg₁) (f_18 hg₂)
    (t_ldp64 hrun₁ (f_18 hg₁) (a := X0 c₁ + BitVec.ofNat 64 32) (ha := by rw [rd_x0])
      (hr1 := h_canRead hg₁.2.2 32 (by decide) (by decide))
      (hr2 := by rw [add8]; exact h_canRead hg₁.2.2 40 (by decide) (by decide)))
    (t_ldp64 hrun₂ (f_18 hg₂) (a := X0 c₂ + BitVec.ofNat 64 32) (ha := by rw [rd_x0])
      (hr1 := h_canRead hg₂.2.2 32 (by decide) (by decide))
      (hr2 := by rw [add8]; exact h_canRead hg₂.2.2 40 (by decide) (by decide)))
    (by simp [leakedValues, evalAddrMode, rd_x0, hX0])
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 440 444]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_1c hg₁) (f_1c hg₂)
    (t_addLsl hrun₁ (f_1c hg₁)) (t_addLsl hrun₂ (f_1c hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 444 448]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_20 hg₁) (f_20 hg₂)
    (t_cset hrun₁ (f_20 hg₁)) (t_cset hrun₂ (f_20 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 448 452]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_24 hg₁) (f_24 hg₂)
    (t_lsl2 hrun₁ (f_24 hg₁)) (t_lsl2 hrun₂ (f_24 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 452 456]
  refine rbody (P := P) (Q := BitVec.ofNat 64 (P.toNat + Q.toNat)) hc hst hsp (f_28 hg₁) (f_28 hg₂)
    (t_lsl2 hrun₁ (f_28 hg₁)) (t_lsl2 hrun₂ (f_28 hg₂)) rfl
    (by simp [upd, e1₁]) (by simp [upd, e1₂]) (by simp [upd, e2₁]) (by simp [upd, e2₂]) ?_
  intro _ _ _ _ e1₁ e1₂ e2₁ e2₂
  rw [pc4 pl.base 456 460]
  have h64 : Q.toNat < 2 ^ 64 := Q.isLt
  have eQ : BitVec.ofNat 64 (P.toNat + Q.toNat) = P + BitVec.ofNat 64 Q.toNat := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  rw [eQ] at e2₁ e2₂
  exact loop2 hc hst hrun₁ hrun₂ F₁ F₂ hsp hX0 K _ _ P _ _ _ _ le_rfl h16 h16d h64 hmsg₁ hmsg₂
    e1₁ e1₂ e2₁ e2₂

end top

end Poly1305DebianCtBlocks

end
end

section
section
/-! # `poly1305_blocks` is constant-time (`ctInternalOk`)

The precondition `blocksPre` gives each run its entry facts (`ctfacts_of_pre`, adapted from the
heap extraction of the functional proof); `blocks_rel` with the continuation "both runs have
returned" gives `ct_subroutine_ok`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At bytesIn)
open Arm64 Arm64.Obj Poly1305DebianCt Leakage Poly1305DebianCtFw

/-- What `blocksPre` gives about an entry state. -/
theorem ctfacts_of_pre {pl : Placement} {X : String → Option (State → State)}
    (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl) {s0 : State} {R : SepProp}
    {ro : Bool} {rh : List (BitVec 8)} {fin : BitVec 8} {msg : List (BitVec 8)}
    (hCL : (prog pl X).CodeLoaded s0.mem)
    (hpre : s0.mem ⊨ blocksPre pl (ro, rh, fin, msg) s0 ∗ R) :
    CtFacts pl X s0 ∧ (s0.readReg64 (.gpr 2#5)).toNat = msg.length ∧ 16 ≤ msg.length ∧
      msg.length % 16 = 0 ∧ MsgOk s0 (s0.readReg64 (.gpr 1#5)) msg.length := by
  obtain ⟨H, hH, hm⟩ := hpre
  obtain ⟨h1, h2, hd12, rfl, hpre1, hR⟩ := hH
  obtain ⟨g1, gA, dg, rfl, ⟨rfl, hφ⟩, hrest⟩ := hpre1
  obtain ⟨q1, qB, d1, rfl, hq1, hqB⟩ := hrest
  obtain ⟨qF, q3, dF, rfl, hqF, hq3⟩ := hqB
  obtain ⟨hl48, hlen, h16, h16d⟩ := hφ
  have hx0 : s0.readReg64 Reg.x0 = X0 s0 := rfl
  rw [hx0] at hq1 hqF
  set X1 := s0.readReg64 Reg.x1 with hX1
  set hh := Heap.empty.union (q1.union (qF.union q3)) with hhh
  have c1 : ∀ j (hj : j < rh.length), q1.phys (X0 s0 + BitVec.ofNat 64 j) = some (.rw rh[j]) :=
    fun j hj => bytes_rw rh _ q1 hq1 j hj
  have cF : qF.phys (X0 s0 + BitVec.ofNat 64 88) = some (.rw fin) := by
    have := bytes_rw [fin] _ qF hqF 0 (by simp)
    simpa using this
  have cM : ∀ j (hj : j < msg.length), Own (q3.phys (X1 + BitVec.ofNat 64 j)) msg[j] := by
    intro j hj
    have := bytesIn_cell hq3 j hj
    cases ro
    · exact Or.inl this
    · exact Or.inr this
  have cS : ∀ j (hj : j < rh.length), hh.phys (X0 s0 + BitVec.ofNat 64 j) = some (.rw rh[j]) :=
    fun j hj => cell_union_right_rw dg (cell_union_left (c1 j hj))
  have cF' : hh.phys (X0 s0 + BitVec.ofNat 64 88) = some (.rw fin) :=
    cell_union_right_rw dg (cell_union_right_rw d1 (cell_union_left cF))
  have cM' : ∀ j (hj : j < msg.length), Own (hh.phys (X1 + BitVec.ofNat 64 j)) msg[j] := fun j hj =>
    own_right dg (own_right d1 (own_right dF (cM j hj)))
  have mt : ∀ a b, Own (hh.phys a) b → s0.mem.read8 a = b ∧ (s0.mem.perm a).r = true ∧
      s0.mem.isLazyFree a = false := fun a b hc => own_matches hm (own_left hc)
  have wdom : ∀ a, W s0 a → ∃ b, hh.phys a = some (.rw b) := by
    intro a w
    obtain ⟨e, ht⟩ := inRegion_eq w
    rw [e, show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, pc_add]
    exact ⟨_, cS _ (by omega)⟩
  have F : CtFacts pl X s0 := {
    good := ⟨hP, hCL, fun a _ => rfl, fun a w => by
      obtain ⟨b, hb⟩ := wdom a w
      have := hm.1 a _ (cell_union_left hb)
      exact ⟨this.2.1, this.2.2, rfl, this.2.1⟩⟩
    rs := fun k hk => ⟨not_inRegion_h (X0 s0) k (Or.inl hk),
      (mt _ _ (Or.inl (cS k (by omega)))).2.1, (mt _ _ (Or.inl (cS k (by omega)))).2.2⟩
    fn := ⟨not_inRegion_h (X0 s0) 88 (Or.inr ⟨by omega, by omega⟩),
      (mt _ _ (Or.inl cF')).2.1, (mt _ _ (Or.inl cF')).2.2⟩ }
  have hmsg : MsgOk s0 X1 msg.length := fun j hj => ⟨by
      intro w
      obtain ⟨e, ht⟩ := inRegion_eq w
      rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, pc_add] at e
      have h := c1 (24 + (X1 + BitVec.ofNat 64 j - (X0 s0 + BitVec.ofNat 64 24)).toNat) (by omega)
      rw [← e] at h
      exact disj_own d1 h (own_right dF (cM j hj)),
    (mt _ _ (cM' j hj)).2.1, (mt _ _ (cM' j hj)).2.2⟩
  exact ⟨F, hlen, h16, h16d, hmsg⟩

theorem ctInternalOk_poly1305_blocks_dev :
    ctInternalOk "poly1305_blocks [libsodium_la_poly1305_donna]" blocksPre blocksPub := by
  refine ⟨by decide, ?_⟩
  intro pl hP _ X _ _ _
  intro x₁ x₂ R₁ R₂ s₁ s₂ he1 he2 hl1 hl2 hp1 hp2 hsame _
  obtain ⟨ro₁, rh₁, fin₁, msg₁⟩ := x₁
  obtain ⟨ro₂, rh₂, fin₂, msg₂⟩ := x₂
  obtain ⟨hpc₁, hrun₁, -⟩ := he1
  obtain ⟨hpc₂, hrun₂, -⟩ := he2
  obtain ⟨F₁, hlen₁, h16, h16d, hmsg₁⟩ := ctfacts_of_pre (X := X) hP hl1 hp1
  obtain ⟨F₂, hlen₂, -, -, hmsg₂⟩ := ctfacts_of_pre (X := X) hP hl2 hp2
  have e2 := sameExceptMem_eq hsame
  have hlr : s₁.readReg64 Reg.lr = s₂.readReg64 Reg.lr := by rw [e2]; rfl
  have hsp : s₁.sp = s₂.sp := by rw [e2]
  have hX0 : X0 s₁ = X0 s₂ := by rw [e2]; rfl
  have hx1 : s₁.readReg64 (.gpr 1#5) = s₂.readReg64 (.gpr 1#5) := by rw [e2]; rfl
  have hx2 : s₁.readReg64 (.gpr 2#5) = s₂.readReg64 (.gpr 2#5) := by rw [e2]; rfl
  have hl₂ : msg₂.length = msg₁.length := by rw [← hlen₁, ← hlen₂, hx2]
  rw [hl₂, ← hx1] at hmsg₂
  rw [← hlen₁] at h16 h16d hmsg₁ hmsg₂
  refine blocks_rel (stopCompat_sub hlr hsp) hrun₁ hrun₂ hpc₁ hpc₂ F₁ F₂ hsp hX0 hx1 hx2 h16 h16d
    hmsg₁ hmsg₂ ?_
  intro m₁ m₂ ps₁ ps₂ r₁ r₂ _ _
  exact oe_stop (Or.inl ⟨rfl, rfl, hrun₁⟩) (Or.inl ⟨rfl, rfl, hrun₂⟩)

end Poly1305DebianCtBlocks

end
end

section
open Poly1305DebianCt

theorem solution :
    ctInternalOk "poly1305_blocks [libsodium_la_poly1305_donna]" blocksPre blocksPub := by
  apply Poly1305DebianCtBlocks.ctInternalOk_poly1305_blocks_dev <;> assumption

end
