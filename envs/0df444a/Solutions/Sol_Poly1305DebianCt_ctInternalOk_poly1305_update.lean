-- Prove2me | solution 1 for Poly1305DebianCt.ctInternalOk_poly1305_update
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-26T19:00:44.728497+00:00
-- url     : https://prove2.me/submissions/3676fc21-86b6-4f97-8ad8-56c27b469fc2

import Definitions.Def_Poly1305DebianCt_PlacedObj
import Definitions.Def_Poly1305DebianCt_Spec
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Definitions.Def_Poly1305Libsodium_Spec
import Mathlib.Tactic.ClearExcept
import Definitions.Def_Arm64_Leakage
import Definitions.Def_Link_LinkOk
import Theorems.Thm_Arm64Facts_steps_codeLoaded_v2

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

theorem bytesIn_mod {ro : Bool} {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap} (m : Memory)
    (hb : (bytesIn ro a bs).holds h)
    (hv : ∀ k (hk : k < bs.length), m.read8 (a + BitVec.ofNat 64 k) = bs[k]) :
    (bytesIn ro a bs).holds (modHeap h m) := by
  cases ro
  · have := modHeap_bytes bs a h m hb
    have e : (List.range bs.length).map (fun j => m.read8 (a + BitVec.ofNat 64 j)) = bs := by
      apply List.ext_getElem (by simp)
      intro j h1 h2; simp only [List.getElem_map, List.getElem_range]; exact hv j h2
    rw [e] at this; exact this
  · rw [modHeap_ro bs a h m hb]; exact hb

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

/-- Both runs execute instruction `i`, fetched at the same `pc`, revealing the same values. -/
theorem oe_exec (hc : StopCompat stop₁ stop₂) {s₁ s₂ : State} {i : Instr}
    (hpc : s₁.pc = s₂.pc) (hsp : s₁.sp = s₂.sp)
    (hr1 : s₁.status = .Running) (hr2 : s₂.status = .Running)
    (hf1 : p.fetchMem s₁.mem s₁.pc = some i) (hf2 : p.fetchMem s₂.mem s₂.pc = some i)
    (hl : leakedValues i s₁ = leakedValues i s₂)
    (h : ObsEquiv p ar stop₁ stop₂ (p.evalInst i s₁) (p.evalInst i s₂)) :
    ObsEquiv p ar stop₁ stop₂ s₁ s₂ := by
  have hstop := hc s₁ s₂ hpc hsp (hr1.trans hr2.symm)
  have hobs : stepObs p ar s₁ = stepObs p ar s₂ := by
    rw [stepObs_exec hf1, stepObs_exec hf2, hpc, hl]
  refine ⟨obsIncluded_of_step hstop hobs ?_, obsIncluded_of_step hstop.symm hobs.symm ?_⟩
  · intro s₁' hs
    rw [step_exec_eq hf1 hs]
    exact ⟨_, Step.exec hr2 hf2, h.1⟩
  · intro s₂' hs
    rw [step_exec_eq hf2 hs]
    exact ⟨_, Step.exec hr1 hf1, h.2⟩

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

end Poly1305DebianCtBlocks

end
end

section
section
/-! # Calling `poly1305_blocks` from a caller that keeps memory in separation logic

`blocks_rel_sep` is `blocks_rel` with the entry facts given as `c.mem ⊨ blocksPre … c ∗ F` (any
frame `F`) and the continuation given the same assertion again on the return memory, with new
accumulator bytes `rh'` (`post_of_memOk`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtBlocks

open Poly1305Libsodium (u64At bytesIn)
open Arm64 Arm64.Obj Poly1305DebianCt Leakage Poly1305DebianCtFw

/-- After a run that changed memory only in the accumulator (`MemOk c m`), the precondition holds
again with the accumulator bytes read from `m`. -/
theorem post_of_memOk {pl : Placement} {c : State} {F : SepProp}
    {ro : Bool} {rh : List (BitVec 8)} {fin : BitVec 8} {msg : List (BitVec 8)}
    (hpre : c.mem ⊨ blocksPre pl (ro, rh, fin, msg) c ∗ F) {m : Memory} (hok : MemOk c m) :
    ∃ rh' : List (BitVec 8), m ⊨ blocksPre pl (ro, rh', fin, msg) c ∗ F := by
  obtain ⟨H, hH, hm⟩ := hpre
  obtain ⟨h1, h2, hd12, rfl, hpre1, hR⟩ := hH
  obtain ⟨g1, gA, dg, rfl, ⟨rfl, hφ⟩, hrest⟩ := hpre1
  obtain ⟨q1, qB, d1, rfl, hq1, hqB⟩ := hrest
  obtain ⟨qF, q3, dF, rfl, hqF, hq3⟩ := hqB
  obtain ⟨hl48, hlen, h16, h16d⟩ := hφ
  have hx0 : c.readReg64 Reg.x0 = X0 c := rfl
  rw [hx0] at hq1 hqF
  set X1 := c.readReg64 Reg.x1 with hX1
  set hh := Heap.empty.union (q1.union (qF.union q3)) with hhh
  have c1 : ∀ j (hj : j < rh.length), q1.phys (X0 c + BitVec.ofNat 64 j) = some (.rw rh[j]) :=
    fun j hj => bytes_rw rh _ q1 hq1 j hj
  have cF : qF.phys (X0 c + BitVec.ofNat 64 88) = some (.rw fin) := by
    have := bytes_rw [fin] _ qF hqF 0 (by simp)
    simpa using this
  have cM : ∀ j (hj : j < msg.length), Own (q3.phys (X1 + BitVec.ofNat 64 j)) msg[j] := by
    intro j hj
    have := bytesIn_cell hq3 j hj
    cases ro
    · exact Or.inl this
    · exact Or.inr this
  have cS : ∀ j (hj : j < rh.length), hh.phys (X0 c + BitVec.ofNat 64 j) = some (.rw rh[j]) :=
    fun j hj => cell_union_right_rw dg (cell_union_left (c1 j hj))
  have cF' : hh.phys (X0 c + BitVec.ofNat 64 88) = some (.rw fin) :=
    cell_union_right_rw dg (cell_union_right_rw d1 (cell_union_left cF))
  have cM' : ∀ j (hj : j < msg.length), Own (hh.phys (X1 + BitVec.ofNat 64 j)) msg[j] := fun j hj =>
    own_right dg (own_right d1 (own_right dF (cM j hj)))
  have mt : ∀ a b, Own (hh.phys a) b → c.mem.read8 a = b ∧ (c.mem.perm a).r = true ∧
      c.mem.isLazyFree a = false := fun a b hc => own_matches hm (own_left hc)
  have wdom : ∀ a, W c a → ∃ b, hh.phys a = some (.rw b) := by
    intro a w
    obtain ⟨e, ht⟩ := inRegion_eq w
    rw [e, show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, pc_add]
    exact ⟨_, cS _ (by omega)⟩
  have fnW : ¬ W c (X0 c + BitVec.ofNat 64 88) :=
    not_inRegion_h (X0 c) 88 (Or.inr ⟨by omega, by omega⟩)
  have hmsgW : ∀ j < msg.length, ¬ W c (X1 + BitVec.ofNat 64 j) := fun j hj => by
    intro w
    obtain ⟨e, ht⟩ := inRegion_eq w
    rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, pc_add] at e
    have h := c1 (24 + (X1 + BitVec.ofNat 64 j - (X0 c + BitVec.ofNat 64 24)).toNat) (by omega)
    rw [← e] at h
    exact disj_own d1 h (own_right dF (cM j hj))
  have h2eq := modHeap_frame hd12 hm hok wdom
  have D := modHeap_disjoint hd12 m
  have D0 := modHeap_disjoint dg m
  have D1 := modHeap_disjoint d1 m
  have DF := modHeap_disjoint dF m
  rw [h2eq, modHeap_union, modHeap_empty] at D
  simp only [modHeap_union, modHeap_empty] at D0
  rw [modHeap_union] at D1
  refine ⟨(List.range rh.length).map fun j => m.read8 (X0 c + BitVec.ofNat 64 j),
    modHeap (hh.union h2) m, ?_,
    modHeap_matches hm hok fun a w => by
      obtain ⟨b, hb⟩ := wdom a w; exact ⟨b, cell_union_left hb⟩⟩
  rw [modHeap_union, h2eq, hhh, modHeap_union, modHeap_empty]
  simp only [modHeap_union] at D ⊢
  refine ⟨_, h2, D, rfl, ?_, hR⟩
  refine ⟨Heap.empty, _, D0, rfl, ⟨rfl, by simp [hl48], hlen, h16, h16d⟩, ?_⟩
  refine ⟨modHeap q1 m, _, D1, rfl, modHeap_bytes rh _ q1 m hq1, modHeap qF m, _, DF, rfl, ?_, ?_⟩
  · exact bytesIn_mod (ro := false) m (a := X0 c + 88#64) (bs := [fin]) hqF (fun k hk => by
      have : k = 0 := by simp at hk; omega
      subst this
      simpa [read8_of_notW hok fnW] using (mt _ _ (Or.inl cF')).1)
  · exact bytesIn_mod m hq3 (fun k hk => by
      rw [read8_of_notW hok (hmsgW k hk)]; exact (mt _ _ (cM' k hk)).1)

end Poly1305DebianCtBlocks

end
end

section
section
/-! # Separation-logic heap algebra

Ported from google-deepmind/code-verification @ 8c8d371f (Apache-2.0),
`arm64-semantics/ProofLib/CoreLemmas.lean` and `ProofLib/SepLogic/Model.lean`: the plain lemmas
about `Heap.Disjoint`, `Heap.union`, `Heap.Matches` and `sepConj`, with ProofLib's custom simp
attributes removed. -/

set_option autoImplicit false

namespace Arm64

namespace SepProp
theorem satisfies_iff {P : SepProp} {m : Memory} :
    (m ⊨ P) ↔ ∃ h : Heap, P.holds h ∧ h.Matches m := Iff.rfl
theorem entails_iff {P Q : SepProp} : (P ⊢ Q) ↔ ∀ h : Heap, P.holds h → Q.holds h := Iff.rfl
theorem holds_emp_iff {h : Heap} : (emp : SepProp).holds h ↔ h = Heap.empty := Iff.rfl
theorem holds_sepConj_iff {P Q : SepProp} {h : Heap} :
    (P ∗ Q).holds h ↔
      ∃ h₁ h₂ : Heap, h₁.Disjoint h₂ ∧ h = h₁.union h₂ ∧ P.holds h₁ ∧ Q.holds h₂ := Iff.rfl
theorem holds_sepExists_iff {α : Sort _} {P : α → SepProp} {h : Heap} :
    (sepExists P).holds h ↔ ∃ x, (P x).holds h := Iff.rfl
end SepProp

theorem holds_pointsTo8_iff {a : BitVec 64} {v : BitVec 8} {h : Heap} :
    (pointsTo8 a v).holds h ↔ h = Heap.singleton a v := Iff.rfl
theorem holds_pointsTo8RO_iff {a : BitVec 64} {v : BitVec 8} {h : Heap} :
    (pointsTo8RO a v).holds h ↔ h = Heap.singletonRO a v := Iff.rfl

namespace Heap

theorem Disjoint.symm {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) : h₂.Disjoint h₁ := by
  refine ⟨fun a => ?_, fun γ k => (hd.2.1 γ k).symm, fun γ k => (hd.2.2.1 γ k).symm,
    fun γ k oa v h => hd.2.2.2.1 γ k oa v h.symm, fun a => (hd.2.2.2.2 a).symm⟩
  rcases hd.1 a with h1 | h2 | ⟨b, h1, h2⟩
  · exact Or.inr (Or.inl h1)
  · exact Or.inl h2
  · exact Or.inr (Or.inr ⟨b, h2, h1⟩)

theorem Disjoint.of_phys_left {h₁ h₂ : Heap}
    (ha : h₁.auth = fun _ _ => none := by rfl)
    (hf : h₁.frag = fun _ _ => none := by rfl)
    (hp : ∀ a, h₁.phys a = none ∨ h₂.phys a = none ∨
      ∃ b, h₁.phys a = some (.ro b) ∧ h₂.phys a = some (.ro b))
    (hm : h₁.mapped = fun _ => false := by rfl) :
    h₁.Disjoint h₂ := by
  refine ⟨hp, fun γ k => Or.inl (congrFun (congrFun ha γ) k),
    fun γ k => Or.inl (congrFun (congrFun hf γ) k), fun γ k oa v h => ?_,
    fun a => Or.inl (congrFun hm a)⟩
  rcases h with ⟨h1, _⟩ | ⟨_, h1⟩
  · rw [congrFun (congrFun ha γ) k] at h1; contradiction
  · rw [congrFun (congrFun hf γ) k] at h1; contradiction

@[simp]
theorem disjoint_empty_left (h : Heap) : Heap.empty.Disjoint h :=
  Disjoint.of_phys_left rfl rfl (fun _ => Or.inl rfl)

@[simp]
theorem disjoint_empty_right (h : Heap) : h.Disjoint Heap.empty :=
  (disjoint_empty_left h).symm

@[simp]
theorem union_empty_left (h : Heap) : Heap.empty.union h = h := by
  cases h; rfl

@[simp]
theorem union_empty_right (h : Heap) : h.union Heap.empty = h := by
  apply Heap.ext
  · funext a; dsimp [union, empty]; cases h.phys a <;> rfl
  · funext γ k; dsimp [union, empty]; cases h.auth γ k <;> rfl
  · funext γ k; dsimp [union, empty]; cases h.frag γ k <;> rfl
  · funext a; dsimp [union, empty]; cases h.mapped a <;> rfl

theorem union_comm_of_disjoint {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) :
    h₁.union h₂ = h₂.union h₁ := by
  apply Heap.ext
  · funext a; dsimp [union]
    rcases hd.1 a with h1 | h2 | ⟨b, h1, h2⟩
    · rw [h1]; cases h₂.phys a <;> rfl
    · rw [h2]; cases h₁.phys a <;> rfl
    · rw [h1, h2]
  · funext γ k; dsimp [union]
    rcases hd.2.1 γ k with h1 | h2
    · rw [h1]; cases h₂.auth γ k <;> rfl
    · rw [h2]; cases h₁.auth γ k <;> rfl
  · funext γ k; dsimp [union]
    rcases hd.2.2.1 γ k with h1 | h2
    · rw [h1]; cases h₂.frag γ k <;> rfl
    · rw [h2]; cases h₁.frag γ k <;> rfl
  · funext a; dsimp [union]
    rcases hd.2.2.2.2 a with h1 | h2
    · rw [h1]; cases h₂.mapped a <;> rfl
    · rw [h2]; cases h₁.mapped a <;> rfl

theorem union_assoc (h₁ h₂ h₃ : Heap) :
    (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃) := by
  apply Heap.ext
  · funext a; dsimp [union]; cases h₁.phys a <;> rfl
  · funext γ k; dsimp [union]; cases h₁.auth γ k <;> rfl
  · funext γ k; dsimp [union]; cases h₁.frag γ k <;> rfl
  · funext a; dsimp [union]; cases h₁.mapped a <;> rfl

theorem disjoint_union_left {h₁ h₂ h₃ : Heap} (hd12 : h₁.Disjoint h₂) :
    (h₁.union h₂).Disjoint h₃ ↔ h₁.Disjoint h₃ ∧ h₂.Disjoint h₃ := by
  constructor
  · intro hd
    have hphys1 : ∀ a, h₁.phys a = none ∨ h₃.phys a = none ∨
        ∃ b, h₁.phys a = some (.ro b) ∧ h₃.phys a = some (.ro b) := by
      intro a
      rcases hd.1 a with hu | h3 | ⟨b, hu, h3⟩
      · dsimp [union] at hu; cases h : h₁.phys a <;> simp_all
      · exact Or.inr (Or.inl h3)
      · dsimp [union] at hu
        cases h : h₁.phys a with
        | none => exact Or.inl rfl
        | some c => rw [h] at hu; exact Or.inr (Or.inr ⟨b, hu, h3⟩)
    have hphys2 : ∀ a, h₂.phys a = none ∨ h₃.phys a = none ∨
        ∃ b, h₂.phys a = some (.ro b) ∧ h₃.phys a = some (.ro b) := by
      intro a
      rcases hd.1 a with hu | h3 | ⟨b, hu, h3⟩
      · dsimp [union] at hu; cases h : h₁.phys a <;> simp_all
      · exact Or.inr (Or.inl h3)
      · dsimp [union] at hu
        cases h : h₁.phys a with
        | none => rw [h] at hu; exact Or.inr (Or.inr ⟨b, hu, h3⟩)
        | some c =>
          rw [h] at hu
          rcases hd12.1 a with h1 | h2 | ⟨b', h1, h2⟩
          · rw [h] at h1; contradiction
          · exact Or.inl h2
          · rw [h1] at h; cases h; cases hu; exact Or.inr (Or.inr ⟨b, h2, h3⟩)
    have hauth1 : ∀ γ k, h₁.auth γ k = none ∨ h₃.auth γ k = none := by
      intro γ k
      rcases hd.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.auth γ k <;> simp_all
      · exact Or.inr h3
    have hauth2 : ∀ γ k, h₂.auth γ k = none ∨ h₃.auth γ k = none := by
      intro γ k
      rcases hd.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.auth γ k <;> simp_all
      · exact Or.inr h3
    have hfrag1 : ∀ γ k, h₁.frag γ k = none ∨ h₃.frag γ k = none := by
      intro γ k
      rcases hd.2.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.frag γ k <;> simp_all
      · exact Or.inr h3
    have hfrag2 : ∀ γ k, h₂.frag γ k = none ∨ h₃.frag γ k = none := by
      intro γ k
      rcases hd.2.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.frag γ k <;> simp_all
      · exact Or.inr h3
    have hcompat1 : ∀ γ k oa v,
        ((h₁.auth γ k = some oa ∧ h₃.frag γ k = some v) ∨
         (h₃.auth γ k = some oa ∧ h₁.frag γ k = some v)) → oa = some v := by
      intro γ k oa v h
      apply hd.2.2.2.1 γ k oa v
      rcases h with ⟨ha, hf⟩ | ⟨ha, hf⟩
      ·exact Or.inl ⟨by dsimp [union]; rw [ha], hf⟩
      · exact Or.inr ⟨ha, by dsimp [union]; rw [hf]⟩
    have hcompat2 : ∀ γ k oa v,
        ((h₂.auth γ k = some oa ∧ h₃.frag γ k = some v) ∨
         (h₃.auth γ k = some oa ∧ h₂.frag γ k = some v)) → oa = some v := by
      intro γ k oa v h
      apply hd.2.2.2.1 γ k oa v
      rcases h with ⟨ha, hf⟩ | ⟨ha, hf⟩
      · rcases hd12.2.1 γ k with h1 | h2
        · exact Or.inl ⟨by dsimp [union]; rw [h1, ha], hf⟩
        · rw [ha] at h2; contradiction
      · rcases hd12.2.2.1 γ k with h1 | h2
        · exact Or.inr ⟨ha, by dsimp [union]; rw [h1, hf]⟩
        · rw [hf] at h2; contradiction
    have hmapped1 : ∀ a, h₁.mapped a = false ∨ h₃.mapped a = false := by
      intro a
      rcases hd.2.2.2.2 a with hu | h3
      · dsimp [union] at hu; cases h : h₁.mapped a <;> simp_all
      · exact Or.inr h3
    have hmapped2 : ∀ a, h₂.mapped a = false ∨ h₃.mapped a = false := by
      intro a
      rcases hd.2.2.2.2 a with hu | h3
      · dsimp [union] at hu; cases h : h₁.mapped a <;> simp_all
      · exact Or.inr h3
    exact ⟨⟨hphys1, hauth1, hfrag1, hcompat1, hmapped1⟩, ⟨hphys2, hauth2, hfrag2, hcompat2, hmapped2⟩⟩
  · rintro ⟨hd1, hd2⟩
    refine ⟨fun a => ?_, fun γ k => ?_, fun γ k => ?_, fun γ k oa v h => ?_, fun a => ?_⟩
    · dsimp [union]
      cases h : h₁.phys a with
      | none => exact hd2.1 a
      | some c =>
        rcases hd1.1 a with h1 | h3 | ⟨b, h1, h3⟩
        · rw [h] at h1; contradiction
        · exact Or.inr (Or.inl h3)
        · rw [h] at h1; exact Or.inr (Or.inr ⟨b, h1, h3⟩)
    · dsimp [union]
      cases h : h₁.auth γ k with
      | none => exact hd2.2.1 γ k
      | some oa =>
        rcases hd1.2.1 γ k with h1 | h3
        · rw [h] at h1; contradiction
        · exact Or.inr h3
    · dsimp [union]
      cases h : h₁.frag γ k with
      | none => exact hd2.2.2.1 γ k
      | some v =>
        rcases hd1.2.2.1 γ k with h1 | h3
        · rw [h] at h1; contradiction
        · exact Or.inr h3
    · rcases h with ⟨ha, hf⟩ | ⟨ha, hf⟩
      · dsimp [union] at ha
        cases h1 : h₁.auth γ k with
        | none =>
          rw [h1] at ha
          exact hd2.2.2.2.1 γ k oa v (Or.inl ⟨ha, hf⟩)
        | some oa' =>
          rw [h1] at ha; cases ha
          exact hd1.2.2.2.1 γ k oa v (Or.inl ⟨h1, hf⟩)
      · dsimp [union] at hf
        cases h1 : h₁.frag γ k with
        | none =>
          rw [h1] at hf
          exact hd2.2.2.2.1 γ k oa v (Or.inr ⟨ha, hf⟩)
        | some v' =>
          rw [h1] at hf; cases hf
          exact hd1.2.2.2.1 γ k oa v (Or.inr ⟨ha, h1⟩)
    · dsimp [union]
      cases h : h₁.mapped a with
      | false => exact hd2.2.2.2.2 a
      | true =>
        rcases hd1.2.2.2.2 a with h1 | h3
        · rw [h] at h1; contradiction
        · exact Or.inr h3

theorem disjoint_union_right {h₁ h₂ h₃ : Heap} (hd23 : h₂.Disjoint h₃) :
    h₁.Disjoint (h₂.union h₃) ↔ h₁.Disjoint h₂ ∧ h₁.Disjoint h₃ := by
  constructor
  · intro hd
    have hd' := (disjoint_union_left hd23).mp hd.symm
    exact ⟨hd'.1.symm, hd'.2.symm⟩
  · rintro ⟨hd1, hd2⟩
    exact ((disjoint_union_left hd23).mpr ⟨hd1.symm, hd2.symm⟩).symm

theorem GhostValid.of_union_left {h₁ h₂ : Heap} (hv : (h₁.union h₂).GhostValid) :
    h₁.GhostValid := by
  rcases hv with ⟨b, hb⟩
  refine ⟨b, fun γ hγ k => ?_⟩
  have ⟨hau, hfu⟩ := hb γ hγ k
  dsimp [Heap.union] at hau hfu
  constructor
  · cases h : h₁.auth γ k with
    | none => rfl
    | some _ => rw [h] at hau; contradiction
  · cases h : h₁.frag γ k with
    | none => rfl
    | some _ => rw [h] at hfu; contradiction

theorem Matches.of_union_left {h₁ h₂ : Heap} {m : Memory}
    (hm : (h₁.union h₂).Matches m) :
    h₁.Matches m :=
  ⟨fun a c h1 => hm.1 a c (by dsimp [Heap.union]; rw [h1]),
    GhostValid.of_union_left hm.2.1,
    fun a h1 => hm.2.2 a (by dsimp [Heap.union]; rw [h1, Bool.true_or])⟩

end Heap

theorem Entails.refl (P : SepProp) : P ⊢ P := SepProp.entails_iff.mpr fun _ h => h

theorem Entails.trans {P Q R : SepProp} (h1 : P ⊢ Q) (h2 : Q ⊢ R) : P ⊢ R :=
  SepProp.entails_iff.mpr fun h hp => SepProp.entails_iff.mp h2 h (SepProp.entails_iff.mp h1 h hp)

theorem Satisfies.mono {P Q : SepProp} (h : P ⊢ Q) {m : Memory} (hm : m ⊨ P) : m ⊨ Q := by
  rcases SepProp.satisfies_iff.mp hm with ⟨hp, hP, hM⟩
  exact SepProp.satisfies_iff.mpr ⟨hp, SepProp.entails_iff.mp h hp hP, hM⟩











theorem sepConj_comm (P Q : SepProp) : (P ∗ Q) = (Q ∗ P) := by
  ext h
  simp only [SepProp.holds_sepConj_iff]
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, hp, hq⟩
    exact ⟨h₂, h₁, hd.symm, Heap.union_comm_of_disjoint hd, hq, hp⟩
  · rintro ⟨h₁, h₂, hd, rfl, hq, hp⟩
    exact ⟨h₂, h₁, hd.symm, Heap.union_comm_of_disjoint hd, hp, hq⟩



@[simp]
theorem sepConj_assoc (P Q R : SepProp) : ((P ∗ Q) ∗ R) = (P ∗ (Q ∗ R)) := by
  ext h
  simp only [SepProp.holds_sepConj_iff]
  constructor
  · rintro ⟨h₁₂, h₃, hd12_3, rfl, ⟨h₁, h₂, hd1_2, rfl, hp, hq⟩, hr⟩
    have ⟨hd1_3, hd2_3⟩ := (Heap.disjoint_union_left hd1_2).mp hd12_3
    exact ⟨h₁, h₂.union h₃, (Heap.disjoint_union_right hd2_3).mpr ⟨hd1_2, hd1_3⟩,
      Heap.union_assoc h₁ h₂ h₃, hp, ⟨h₂, h₃, hd2_3, rfl, hq, hr⟩⟩
  · rintro ⟨h₁, h₂₃, hd1_23, rfl, hp, ⟨h₂, h₃, hd2_3, rfl, hq, hr⟩⟩
    have ⟨hd1_2, hd1_3⟩ := (Heap.disjoint_union_right hd2_3).mp hd1_23
    exact ⟨h₁.union h₂, h₃, (Heap.disjoint_union_left hd1_2).mpr ⟨hd1_3, hd2_3⟩,
      (Heap.union_assoc h₁ h₂ h₃).symm, ⟨h₁, h₂, hd1_2, rfl, hp, hq⟩, hr⟩

instance instAssociativeSepConj : Std.Associative SepProp.sepConj where
  assoc := sepConj_assoc

instance instCommutativeSepConj : Std.Commutative SepProp.sepConj where
  comm := sepConj_comm

theorem Entails.of_eq {P Q : SepProp} (heq : P = Q := by ac_rfl) : P ⊢ Q :=
  heq ▸ Entails.refl P

theorem Satisfies.of_eq {P Q : SepProp} {m : Memory}
    (h : m ⊨ P) (heq : P = Q := by ac_rfl) : m ⊨ Q :=
  heq ▸ h

@[simp]
theorem emp_sepConj (P : SepProp) : (SepProp.emp ∗ P) = P := by
  ext h
  simp only [SepProp.holds_sepConj_iff, SepProp.holds_emp_iff]
  constructor
  · rintro ⟨h₁, h₂, _, rfl, rfl, hp⟩
    simpa using hp
  · intro hp
    exact ⟨Heap.empty, h, Heap.disjoint_empty_left h, (Heap.union_empty_left h).symm, rfl, hp⟩

@[simp]
theorem sepConj_emp (P : SepProp) : (P ∗ SepProp.emp) = P := by
  rw [sepConj_comm, emp_sepConj]


end Arm64

end
end

section
section
/-! # Byte-slice ownership: reads, writes, splits

Plain-Lean replacements for the parts of DeepMind's ProofLib (google-deepmind/code-verification
@ 8c8d371f, Apache-2.0, `ProofLib/SepLogic/Bytes.lean`) that the x25519 ladder proofs use:
`a ↦ₛ bs` owns `bs` at `a`; a store to an owned byte updates the list; `pointsTo64` and `memRegion`
are byte slices. -/

set_option autoImplicit false

namespace Arm64

theorem pointsToBytes_cons (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    (a ↦ₛ (b :: bs)) = (a ↦₈ b) ∗ ((a + 1#64) ↦ₛ bs) := rfl
theorem pointsToBytes_nil (a : BitVec 64) : (a ↦ₛ ([] : List (BitVec 8))) = emp := rfl
theorem pointsToBytesRO_cons (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    (a ↦ᵣ (b :: bs)) = (a ↦₈ᵣ b) ∗ ((a + 1#64) ↦ᵣ bs) := rfl
theorem pointsToBytesRO_nil (a : BitVec 64) : (a ↦ᵣ ([] : List (BitVec 8))) = emp := rfl

namespace Heap

/-- `h` with the cell at `x` replaced by `c`. -/
def upd (h : Heap) (x : BitVec 64) (c : HeapCell) : Heap :=
  { h with phys := fun y => if y = x then some c else h.phys y }

theorem upd_union_left (h₁ h₂ : Heap) (x : BitVec 64) (c : HeapCell) :
    (h₁.union h₂).upd x c = (h₁.upd x c).union h₂ := by
  apply Heap.ext
  · funext y; by_cases hy : y = x <;> simp [upd, union, hy]
  · rfl
  · rfl
  · rfl

theorem upd_union_right (h₁ h₂ : Heap) (x : BitVec 64) (c : HeapCell) (hx : h₁.phys x = none) :
    (h₁.union h₂).upd x c = h₁.union (h₂.upd x c) := by
  apply Heap.ext
  · funext y; by_cases hy : y = x
    · subst hy; simp [upd, union, hx]
    · simp [upd, union, hy]
  · rfl
  · rfl
  · rfl

theorem Disjoint.upd_left {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) {x : BitVec 64} (c : HeapCell)
    (hx : h₂.phys x = none) : (h₁.upd x c).Disjoint h₂ := by
  refine ⟨fun y => ?_, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2⟩
  by_cases hy : y = x
  · subst hy; exact Or.inr (Or.inl hx)
  · simp only [upd, hy, if_false]; exact hd.1 y

theorem Disjoint.upd_right {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) {x : BitVec 64} (c : HeapCell)
    (hx : h₁.phys x = none) : h₁.Disjoint (h₂.upd x c) :=
  (hd.symm.upd_left c hx).symm

theorem rw_phys_right_none {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) {x : BitVec 64} {b : BitVec 8}
    (hx : h₁.phys x = some (.rw b)) : h₂.phys x = none := by
  rcases hd.1 x with h | h | ⟨b', h1, _⟩
  · rw [hx] at h; cases h
  · exact h
  · rw [hx] at h1; cases h1

theorem rw_phys_left_none {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) {x : BitVec 64} {b : BitVec 8}
    (hx : h₂.phys x = some (.rw b)) : h₁.phys x = none :=
  rw_phys_right_none hd.symm hx

end Heap

/-! ## Memory facts about `write8` -/

namespace Memory

theorem read8_write8_same' (m : Memory) (x : BitVec 64) (v : BitVec 8) :
    (m.write8 x v).read8 x = v := by
  simp [write8, read8]

theorem read8_write8_ne' (m : Memory) {x y : BitVec 64} (v : BitVec 8) (h : y ≠ x) :
    (m.write8 x v).read8 y = m.read8 y := by
  simp [write8, read8, h]

theorem perm_write8' (m : Memory) (x y : BitVec 64) (v : BitVec 8) :
    (m.write8 x v).perm y = m.perm y := by
  by_cases h : y = x
  · subst h; simp only [write8, perm, rawPerm, if_true]
    cases hc : m.cells y with
    | none => rfl
    | some c => obtain ⟨p, b⟩ := c; cases p <;> rfl
  · simp [write8, perm, h]

theorem isAnon_write8' (m : Memory) (x y : BitVec 64) (v : BitVec 8) :
    (m.write8 x v).isAnon y = m.isAnon y := by
  by_cases h : y = x
  · subst h; simp only [write8, isAnon, rawPerm, if_true]
    cases hc : m.cells y with
    | none => rfl
    | some c => obtain ⟨p, b⟩ := c; cases p <;> rfl
  · simp [write8, isAnon, h]

theorem isLazyFree_write8_same' (m : Memory) (x : BitVec 64) (v : BitVec 8) :
    (m.write8 x v).isLazyFree x = false := by
  simp only [write8, isLazyFree, rawPerm, if_true]
  cases hc : m.cells x with
  | none => rfl
  | some c => obtain ⟨p, b⟩ := c; cases p <;> rfl

theorem isLazyFree_write8_ne' (m : Memory) {x y : BitVec 64} (v : BitVec 8) (h : y ≠ x) :
    (m.write8 x v).isLazyFree y = m.isLazyFree y := by
  simp [write8, isLazyFree, h]

end Memory

namespace Heap

theorem Matches.upd_write {h : Heap} {m : Memory} (hm : h.Matches m) {x : BitVec 64} {b : BitVec 8}
    (hx : h.phys x = some (.rw b)) (v : BitVec 8) :
    (h.upd x (.rw v)).Matches (m.write8 x v) := by
  refine ⟨fun y c hy => ?_, hm.2.1, fun y hy => ?_⟩
  · by_cases hyx : y = x
    · subst hyx
      simp only [upd, if_true, Option.some.injEq] at hy
      subst hy
      have h0 := hm.1 y _ hx
      simp only at h0
      refine ⟨Memory.read8_write8_same' _ _ _, ?_, Memory.isLazyFree_write8_same' _ _ _⟩
      rw [Memory.perm_write8']; exact h0.2.1
    · simp only [upd, hyx, if_false] at hy
      have h0 := hm.1 y c hy
      rw [Memory.read8_write8_ne' _ _ hyx, Memory.perm_write8', Memory.isLazyFree_write8_ne' _ _ hyx]
      exact h0
  · have h0 := hm.2.2 y hy
    rw [Memory.perm_write8', Memory.isAnon_write8']; exact h0

end Heap

/-! ## Byte slices as heaps -/

theorem bytes_phys : ∀ {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap},
    (a ↦ₛ bs).holds h → ∀ (j : Nat) (hj : j < bs.length),
      h.phys (a + BitVec.ofNat 64 j) = some (.rw bs[j])
  | _, [], _, _, j, hj => by simp at hj
  | a, b :: bs, h, hh, j, hj => by
    obtain ⟨h1, h2, hd, rfl, h1e, h2h⟩ := SepProp.holds_sepConj_iff.mp hh
    rw [holds_pointsTo8_iff] at h1e; subst h1e
    cases j with
    | zero => simp [Heap.union, Heap.singleton]
    | succ j =>
      have ih := bytes_phys h2h j (by simp at hj; omega)
      have ha : a + BitVec.ofNat 64 (j + 1) = a + 1#64 + BitVec.ofNat 64 j := by
        rw [BitVec.add_assoc]; congr 1; bv_omega
      have hne : a + 1#64 + BitVec.ofNat 64 j ≠ a := by
        intro he
        have := Heap.rw_phys_left_none hd ih
        rw [he] at this; simp [Heap.singleton] at this
      rw [ha]
      simp only [Heap.union, Heap.singleton, hne, if_false, ih, List.getElem_cons_succ]

theorem bytesRO_phys : ∀ {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap},
    (a ↦ᵣ bs).holds h → ∀ (j : Nat) (hj : j < bs.length),
      h.phys (a + BitVec.ofNat 64 j) = some (.ro bs[j])
  | _, [], _, _, j, hj => by simp at hj
  | a, b :: bs, h, hh, j, hj => by
    obtain ⟨h1, h2, hd, rfl, h1e, h2h⟩ := SepProp.holds_sepConj_iff.mp hh
    rw [holds_pointsTo8RO_iff] at h1e; subst h1e
    cases j with
    | zero => simp [Heap.union, Heap.singletonRO]
    | succ j =>
      have ih := bytesRO_phys h2h j (by simp at hj; omega)
      have ha : a + BitVec.ofNat 64 (j + 1) = a + 1#64 + BitVec.ofNat 64 j := by
        rw [BitVec.add_assoc]; congr 1; bv_omega
      rw [ha]
      by_cases hne : a + 1#64 + BitVec.ofNat 64 j = a
      · -- both sides own the same read-only cell: the values agree by disjointness
        rcases hd.1 a with h0 | h0 | ⟨c, h1c, h2c⟩
        · simp [Heap.singletonRO] at h0
        · rw [← hne] at h0; rw [ih] at h0; cases h0
        · simp only [Heap.singletonRO, if_true, Option.some.injEq, HeapCell.ro.injEq] at h1c
          rw [← hne] at h2c; rw [ih] at h2c
          simp only [Option.some.injEq, HeapCell.ro.injEq] at h2c
          simp only [Heap.union, Heap.singletonRO, hne, if_true, List.getElem_cons_succ]
          rw [h1c, h2c]
      · simp only [Heap.union, Heap.singletonRO, hne, if_false, ih, List.getElem_cons_succ]

theorem bytes_upd : ∀ {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap},
    (a ↦ₛ bs).holds h → ∀ (j : Nat) (hj : j < bs.length) (v : BitVec 8),
      (a ↦ₛ bs.set j v).holds (h.upd (a + BitVec.ofNat 64 j) (.rw v))
  | _, [], _, _, j, hj, _ => by simp at hj
  | a, b :: bs, h, hh, j, hj, v => by
    obtain ⟨h1, h2, hd, rfl, h1e, h2h⟩ := SepProp.holds_sepConj_iff.mp hh
    rw [holds_pointsTo8_iff] at h1e; subst h1e
    have h2a : h2.phys a = none :=
      Heap.rw_phys_right_none hd (b := b) (by simp [Heap.singleton])
    cases j with
    | zero =>
      simp only [List.set_cons_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      rw [Heap.upd_union_left]
      refine SepProp.holds_sepConj_iff.mpr ⟨Heap.singleton a v, h2, ?_, ?_, rfl, h2h⟩
      · exact Heap.Disjoint.of_phys_left rfl rfl (fun y => by
          by_cases hy : y = a
          · subst hy; exact Or.inr (Or.inl h2a)
          · exact Or.inl (by simp [Heap.singleton, hy])) rfl
      · apply Heap.ext
        · funext y; by_cases hy : y = a <;> simp [Heap.upd, Heap.union, Heap.singleton, hy]
        · rfl
        · rfl
        · rfl
    | succ j =>
      have hj' : j < bs.length := by simp at hj; omega
      have ih := bytes_upd h2h j hj' v
      have ha : a + BitVec.ofNat 64 (j + 1) = a + 1#64 + BitVec.ofNat 64 j := by
        rw [BitVec.add_assoc]; congr 1; bv_omega
      have hph := bytes_phys h2h j hj'
      have hne : a + 1#64 + BitVec.ofNat 64 j ≠ a := by
        intro he; rw [he] at hph; rw [h2a] at hph; cases hph
      have h1x : (Heap.singleton a b).phys (a + 1#64 + BitVec.ofNat 64 j) = none := by
        simp [Heap.singleton, hne]
      rw [ha, Heap.upd_union_right _ _ _ _ h1x, List.set_cons_succ]
      exact SepProp.holds_sepConj_iff.mpr ⟨_, _, hd.upd_right _ h1x, rfl, rfl, ih⟩

/-! ## Satisfaction-level reads and writes -/

theorem sat_bytes_read {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ₛ bs) ∗ F) (j : Nat) (hj : j < bs.length) :
    m.read8 (a + BitVec.ofNat 64 j) = bs[j] ∧ m.perm (a + BitVec.ofNat 64 j) = some Perm.rw ∧
      m.isLazyFree (a + BitVec.ofNat 64 j) = false := by
  obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
  obtain ⟨h1, h2, hd, rfl, h1h, _⟩ := SepProp.holds_sepConj_iff.mp hh
  have hp := bytes_phys h1h j hj
  have := (Heap.Matches.of_union_left hm).1 _ _ hp
  exact this

theorem sat_bytesRO_read {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ᵣ bs) ∗ F) (j : Nat) (hj : j < bs.length) :
    m.read8 (a + BitVec.ofNat 64 j) = bs[j] ∧ (m.perm (a + BitVec.ofNat 64 j)).r = true ∧
      m.isLazyFree (a + BitVec.ofNat 64 j) = false := by
  obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
  obtain ⟨h1, h2, hd, rfl, h1h, _⟩ := SepProp.holds_sepConj_iff.mp hh
  have hp := bytesRO_phys h1h j hj
  have := (Heap.Matches.of_union_left hm).1 _ _ hp
  exact this

theorem sat_bytes_write {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ₛ bs) ∗ F) (j : Nat) (hj : j < bs.length) (v : BitVec 8) :
    (m.write8 (a + BitVec.ofNat 64 j) v) ⊨ (a ↦ₛ bs.set j v) ∗ F := by
  obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
  obtain ⟨h1, h2, hd, rfl, h1h, h2h⟩ := SepProp.holds_sepConj_iff.mp hh
  have hp := bytes_phys h1h j hj
  refine SepProp.satisfies_iff.mpr ⟨(h1.upd (a + BitVec.ofNat 64 j) (.rw v)).union h2, ?_, ?_⟩
  · exact SepProp.holds_sepConj_iff.mpr ⟨_, _, hd.upd_left _ (Heap.rw_phys_right_none hd hp), rfl,
      bytes_upd h1h j hj v, h2h⟩
  · rw [← Heap.upd_union_left]
    exact hm.upd_write (b := bs[j]) (by simp [Heap.union, hp]) v

/-! ## Splitting byte slices -/

theorem pointsToBytes_append (a : BitVec 64) (xs ys : List (BitVec 8)) :
    (a ↦ₛ (xs ++ ys)) = (a ↦ₛ xs) ∗ ((a + BitVec.ofNat 64 xs.length) ↦ₛ ys) := by
  induction xs generalizing a with
  | nil => simp [pointsToBytes_nil]
  | cons x xs ih =>
    rw [List.cons_append, pointsToBytes_cons, pointsToBytes_cons, ih, sepConj_assoc]
    have e : a + 1#64 + BitVec.ofNat 64 xs.length = a + BitVec.ofNat 64 (x :: xs).length := by
      simp only [List.length_cons]; rw [BitVec.add_assoc]; congr 1; bv_omega
    rw [e]

theorem pointsToBytesRO_append (a : BitVec 64) (xs ys : List (BitVec 8)) :
    (a ↦ᵣ (xs ++ ys)) = (a ↦ᵣ xs) ∗ ((a + BitVec.ofNat 64 xs.length) ↦ᵣ ys) := by
  induction xs generalizing a with
  | nil => simp [pointsToBytesRO_nil]
  | cons x xs ih =>
    rw [List.cons_append, pointsToBytesRO_cons, pointsToBytesRO_cons, ih, sepConj_assoc]
    have e : a + 1#64 + BitVec.ofNat 64 xs.length = a + BitVec.ofNat 64 (x :: xs).length := by
      simp only [List.length_cons]; rw [BitVec.add_assoc]; congr 1; bv_omega
    rw [e]

theorem pointsToBytes_split (a : BitVec 64) (bs : List (BitVec 8)) (n : Nat) (hn : n ≤ bs.length) :
    (a ↦ₛ bs) = (a ↦ₛ bs.take n) ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bs.drop n) := by
  have h := pointsToBytes_append a (bs.take n) (bs.drop n)
  rw [List.take_append_drop, List.length_take_of_le hn] at h
  exact h

theorem pointsToBytesRO_split (a : BitVec 64) (bs : List (BitVec 8)) (n : Nat)
    (hn : n ≤ bs.length) :
    (a ↦ᵣ bs) = (a ↦ᵣ bs.take n) ∗ ((a + BitVec.ofNat 64 n) ↦ᵣ bs.drop n) := by
  have h := pointsToBytesRO_append a (bs.take n) (bs.drop n)
  rw [List.take_append_drop, List.length_take_of_le hn] at h
  exact h

/-- Unpack a 64-bit word into its 8 little-endian bytes. -/
def unpack64 (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
   v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8]

@[simp] theorem unpack64_length (v : BitVec 64) : (unpack64 v).length = 8 := rfl

theorem pointsTo64_eq_bytes (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦ₛ unpack64 v) := by
  simp only [pointsTo64, unpack64, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_zero]
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_omega
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by bv_omega
  have h4 : a + 3#64 + 1#64 = a + 4#64 := by bv_omega
  have h5 : a + 4#64 + 1#64 = a + 5#64 := by bv_omega
  have h6 : a + 5#64 + 1#64 = a + 6#64 := by bv_omega
  have h7 : a + 6#64 + 1#64 = a + 7#64 := by bv_omega
  rw [h2, h3, h4, h5, h6, h7]

end Arm64

end
end

section
section
/-! # Regions, existentials and pure facts

`memRegion a n` (a stack frame) is a byte slice of length `n` with unknown contents; pure
assertions and separating existentials move in and out of `⊨`. -/

set_option autoImplicit false

namespace Arm64

theorem sepConj_mono {P P' Q Q' : SepProp} (h1 : P ⊢ P') (h2 : Q ⊢ Q') : (P ∗ Q) ⊢ (P' ∗ Q') := by
  intro h hh
  obtain ⟨h₁, h₂, hd, rfl, hp, hq⟩ := SepProp.holds_sepConj_iff.mp hh
  exact SepProp.holds_sepConj_iff.mpr ⟨h₁, h₂, hd, rfl, h1 _ hp, h2 _ hq⟩

theorem sat_sep_mono {m : Memory} {P P' Q : SepProp} (hs : m ⊨ P ∗ Q) (h1 : P ⊢ P') :
    m ⊨ P' ∗ Q :=
  Satisfies.mono (sepConj_mono h1 (Entails.refl Q)) hs

theorem pure_sepConj_holds {φ : Prop} {P : SepProp} {h : Heap} :
    (⌜φ⌝ ∗ P).holds h ↔ φ ∧ P.holds h := by
  constructor
  · intro hh
    obtain ⟨h₁, h₂, _, rfl, ⟨rfl, hφ⟩, hp⟩ := SepProp.holds_sepConj_iff.mp hh
    exact ⟨hφ, by rw [Heap.union_empty_left]; exact hp⟩
  · rintro ⟨hφ, hp⟩
    exact SepProp.holds_sepConj_iff.mpr ⟨Heap.empty, h, Heap.disjoint_empty_left h,
      (Heap.union_empty_left h).symm, ⟨rfl, hφ⟩, hp⟩

theorem sat_pure_sep {m : Memory} {φ : Prop} {P : SepProp} : (m ⊨ ⌜φ⌝ ∗ P) ↔ φ ∧ (m ⊨ P) := by
  constructor
  · intro hs
    obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
    have := pure_sepConj_holds.mp hh
    exact ⟨this.1, SepProp.satisfies_iff.mpr ⟨h, this.2, hm⟩⟩
  · rintro ⟨hφ, hs⟩
    obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
    exact SepProp.satisfies_iff.mpr ⟨h, pure_sepConj_holds.mpr ⟨hφ, hh⟩, hm⟩

theorem sepExists_sepConj {α : Sort _} (P : α → SepProp) (Q : SepProp) :
    ((∃∗ x, P x) ∗ Q) = ∃∗ x, (P x ∗ Q) := by
  ext h
  simp only [SepProp.holds_sepConj_iff, SepProp.holds_sepExists_iff]
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, ⟨x, hp⟩, hq⟩; exact ⟨x, h₁, h₂, hd, rfl, hp, hq⟩
  · rintro ⟨x, h₁, h₂, hd, rfl, hp, hq⟩; exact ⟨h₁, h₂, hd, rfl, ⟨x, hp⟩, hq⟩

theorem sat_sepExists {m : Memory} {α : Sort _} {P : α → SepProp} :
    (m ⊨ ∃∗ x, P x) ↔ ∃ x, m ⊨ P x := by
  constructor
  · intro hs
    obtain ⟨h, ⟨x, hp⟩, hm⟩ := SepProp.satisfies_iff.mp hs
    exact ⟨x, SepProp.satisfies_iff.mpr ⟨h, hp, hm⟩⟩
  · rintro ⟨x, hs⟩
    obtain ⟨h, hp, hm⟩ := SepProp.satisfies_iff.mp hs
    exact SepProp.satisfies_iff.mpr ⟨h, ⟨x, hp⟩, hm⟩

theorem regionHeap_phys (base : BitVec 64) (len : Nat) (m : Memory) (y : BitVec 64) :
    (regionHeap base len m).phys y =
      if (y - base).toNat < len then some (.rw (m.read8 y)) else none := by
  unfold regionHeap InRegion; exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

/-! ## Byte-slice heaps carry no ghost state and nothing outside the slice -/

theorem bytes_shape : ∀ {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap},
    (a ↦ₛ bs).holds h →
      h.auth = (fun _ _ => none) ∧ h.frag = (fun _ _ => none) ∧ h.mapped = (fun _ => false) ∧
      ∀ y, bs.length ≤ (y - a).toNat → h.phys y = none
  | a, [], h, hh => by
    rw [pointsToBytes_nil, SepProp.holds_emp_iff] at hh; subst hh
    exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  | a, b :: bs, h, hh => by
    obtain ⟨h1, h2, _, rfl, h1e, h2h⟩ := SepProp.holds_sepConj_iff.mp hh
    rw [holds_pointsTo8_iff] at h1e; subst h1e
    obtain ⟨ha, hf, hm, hp⟩ := bytes_shape h2h
    refine ⟨?_, ?_, ?_, fun y hy => ?_⟩
    · funext γ k; simp [Heap.union, Heap.singleton, ha]
    · funext γ k; simp [Heap.union, Heap.singleton, hf]
    · funext y; simp [Heap.union, Heap.singleton, hm]
    · have hya : y ≠ a := by
        intro he; subst he; simp at hy
      have : bs.length ≤ (y - (a + 1#64)).toNat := by
        simp only [List.length_cons] at hy; bv_omega
      simp [Heap.union, Heap.singleton, hya, hp y this]

theorem bytes_entails_memRegion (a : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦ₛ bs) ⊢ memRegion a bs.length := by
  intro h hh
  obtain ⟨ha, hf, hm, hp⟩ := bytes_shape hh
  refine ⟨Memory.ofFn (fun y => bs.getD (y - a).toNat 0), ?_⟩
  show h = regionHeap a bs.length _
  apply Heap.ext
  · funext y
    rw [regionHeap_phys]
    split
    · rename_i hy
      have := bytes_phys hh (y - a).toNat hy
      rw [show a + BitVec.ofNat 64 (y - a).toNat = y by bv_omega] at this
      rw [this]
      simp only [Memory.read8, Memory.ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy,
        Option.getD_some]
    · rename_i hy; exact hp y (by omega)
  · exact ha
  · exact hf
  · exact hm

theorem regionHeap_holds_bytes : ∀ (n : Nat) (a : BitVec 64) (m : Memory), n < 2 ^ 64 →
    (a ↦ₛ m.readBytes a n).holds (regionHeap a n m)
  | 0, a, m, _ => by
    show _ = _
    apply Heap.ext
    · funext y; simp [regionHeap, InRegion, Heap.empty]
    · rfl
    · rfl
    · rfl
  | n + 1, a, m, hn => by
    have ih := regionHeap_holds_bytes n (a + 1#64) m (by omega)
    refine SepProp.holds_sepConj_iff.mpr ⟨Heap.singleton a (m.read8 a), regionHeap (a + 1#64) n m,
      ?_, ?_, rfl, ih⟩
    · exact Heap.Disjoint.of_phys_left rfl rfl (fun y => by
        by_cases hy : y = a
        · subst hy; right; left
          rw [regionHeap_phys, if_neg]; bv_omega
        · left; simp [Heap.singleton, hy]) rfl
    · apply Heap.ext
      · funext y
        by_cases hy : y = a
        · subst hy
          simp only [Heap.union, Heap.singleton, if_true, regionHeap_phys]
          rw [if_pos (by bv_omega)]
        · simp only [Heap.union, Heap.singleton, hy, if_false, regionHeap_phys]
          have e : ((y - a).toNat < n + 1) ↔ ((y - (a + 1#64)).toNat < n) := by
            constructor <;> intro h <;> bv_omega
          by_cases hc : (y - (a + 1#64)).toNat < n
          · rw [if_pos (e.mpr hc), if_pos hc]
          · rw [if_neg (fun h => hc (e.mp h)), if_neg hc]
      · rfl
      · rfl
      · rfl

theorem readBytes_length (m : Memory) : ∀ (a : BitVec 64) (n : Nat), (m.readBytes a n).length = n
  | _, 0 => rfl
  | a, n + 1 => by simp [Memory.readBytes, readBytes_length m (a + 1#64) n]

theorem memRegion_entails_bytes (a : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    memRegion a n ⊢ ∃∗ bs, ⌜bs.length = n⌝ ∗ (a ↦ₛ bs) := by
  intro h hh
  obtain ⟨m, hm⟩ := hh
  change h = regionHeap a n m at hm
  subst hm
  exact ⟨m.readBytes a n, pure_sepConj_holds.mpr ⟨readBytes_length m a n,
    regionHeap_holds_bytes n a m hn⟩⟩

end Arm64

end
end

section
section
/-! # 64-bit cells and byte reads: values and permissions from ownership -/

set_option autoImplicit false

namespace Arm64

theorem concat8_extract (v : BitVec 64) :
    v.extractLsb' 56 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 40 8 ++ v.extractLsb' 32 8 ++
      v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

theorem canRead_of {m : Memory} : ∀ {x : BitVec 64} {n : Nat},
    (∀ i < n, (m.perm (x + BitVec.ofNat 64 i)).r = true ∧
      m.isLazyFree (x + BitVec.ofNat 64 i) = false) → m.canRead x n = true
  | _, 0, _ => rfl
  | x, n + 1, h => by
    have h0 := h 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    have ih := canRead_of (x := x + 1#64) (n := n) (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show x + BitVec.ofNat 64 (i + 1) = x + 1#64 + BitVec.ofNat 64 i by
        rw [BitVec.add_assoc]; congr 1; bv_omega] at this)
    simp only [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree] at ih ⊢
    simp only [Bool.and_eq_true] at ih
    simp [h0.1, h0.2, ih.1, ih.2]

theorem canWrite_of {m : Memory} : ∀ {x : BitVec 64} {n : Nat},
    (∀ i < n, m.perm (x + BitVec.ofNat 64 i) = some Perm.rw) → m.canWrite x n = true
  | _, 0, _ => rfl
  | x, n + 1, h => by
    have h0 := h 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    have ih := canWrite_of (x := x + 1#64) (n := n) (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show x + BitVec.ofNat 64 (i + 1) = x + 1#64 + BitVec.ofNat 64 i by
        rw [BitVec.add_assoc]; congr 1; bv_omega] at this)
    simp only [Memory.canWrite, Memory.allPerm] at ih ⊢
    simp [h0, ih, Perm.rw]

/-- Byte `i` of `unpack64 v`. -/
theorem unpack64_getElem (v : BitVec 64) (i : Nat) (hi : i < 8) :
    (unpack64 v)[i]'(by simp; omega) = v.extractLsb' (8 * i) 8 := by
  interval_cases i <;> rfl

theorem sat64_byte {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F)
    (i : Nat) (hi : i < 8) :
    m.read8 (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * i) 8 ∧
      m.perm (a + BitVec.ofNat 64 i) = some Perm.rw ∧
      m.isLazyFree (a + BitVec.ofNat 64 i) = false := by
  rw [pointsTo64_eq_bytes] at hs
  have := sat_bytes_read hs i (by simp; omega)
  rwa [unpack64_getElem v i hi] at this

theorem sat64_read {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F) :
    m.read64 a = v ∧ m.canRead a 8 = true ∧ m.canWrite a 8 = true := by
  refine ⟨?_, canRead_of (fun i hi => ?_), canWrite_of (fun i hi => (sat64_byte hs i hi).2.1)⟩
  · have h0 := (sat64_byte hs 0 (by omega)).1
    have h1 := (sat64_byte hs 1 (by omega)).1
    have h2 := (sat64_byte hs 2 (by omega)).1
    have h3 := (sat64_byte hs 3 (by omega)).1
    have h4 := (sat64_byte hs 4 (by omega)).1
    have h5 := (sat64_byte hs 5 (by omega)).1
    have h6 := (sat64_byte hs 6 (by omega)).1
    have h7 := (sat64_byte hs 7 (by omega)).1
    simp only [BitVec.ofNat_eq_ofNat, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
    simp only [Memory.read64]
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
    exact concat8_extract v
  · have := sat64_byte hs i hi
    rw [this.2.1]; exact ⟨rfl, this.2.2⟩

theorem sat64_write {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F)
    (w : BitVec 64) : m.write64 a w ⊨ (a ↦₆₄ w) ∗ F := by
  rw [pointsTo64_eq_bytes] at hs ⊢
  have e : ∀ i : Nat, a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 i := fun _ => rfl
  have s0 := sat_bytes_write hs 0 (by simp) (w.extractLsb' 0 8)
  have s1 := sat_bytes_write s0 1 (by simp) (w.extractLsb' 8 8)
  have s2 := sat_bytes_write s1 2 (by simp) (w.extractLsb' 16 8)
  have s3 := sat_bytes_write s2 3 (by simp) (w.extractLsb' 24 8)
  have s4 := sat_bytes_write s3 4 (by simp) (w.extractLsb' 32 8)
  have s5 := sat_bytes_write s4 5 (by simp) (w.extractLsb' 40 8)
  have s6 := sat_bytes_write s5 6 (by simp) (w.extractLsb' 48 8)
  have s7 := sat_bytes_write s6 7 (by simp) (w.extractLsb' 56 8)
  clear e
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at s7
  simp only [Memory.write64, BitVec.add_zero]
  convert s7 using 3
  simp [unpack64]

end Arm64

end
end

section
section
/-! # Abstract machine states

Every state inside a block proof is `mkS s0 pc r sp ps m v`: the state `s0` with the program
counter, the general registers, the stack pointer, the flags, the memory and the vector registers
replaced. The instruction evaluators map such states to such states, and these lemmas let `simp`
compute the result without unfolding `State`. -/

set_option autoImplicit false

namespace Poly1305DebianCtFw
open Poly1305DebianCt

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64

def upd {α : Type} (r : BitVec 5 → α) (i : BitVec 5) (v : α) : BitVec 5 → α :=
  fun j => if j = i then v else r j

@[simp] theorem upd_same {α : Type} (r : BitVec 5 → α) (i : BitVec 5) (v : α) : upd r i v i = v := by
  simp [upd]

theorem upd_ne {α : Type} (r : BitVec 5 → α) {i j : BitVec 5} (v : α) (h : j ≠ i) :
    upd r i v j = r j := by
  simp [upd, h]

/-- `upd` at literal indices: `simp` decides the index comparison. -/
@[simp] theorem upd_apply {α : Type} (r : BitVec 5 → α) (i j : BitVec 5) (v : α) :
    upd r i v j = if j = i then v else r j := rfl

def mkS (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64) (ps : PState)
    (m : Memory) (v : BitVec 5 → BitVec 128) : State :=
  { s0 with pc := pc, regs := ⟨r⟩, sp := sp, pstate := ps, mem := m, vregs := ⟨v⟩ }

section
variable (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64) (ps : PState)
  (m : Memory) (v : BitVec 5 → BitVec 128)

@[simp] theorem mkS_pc : (mkS s0 pc r sp ps m v).pc = pc := rfl
@[simp] theorem mkS_sp : (mkS s0 pc r sp ps m v).sp = sp := rfl
@[simp] theorem mkS_mem : (mkS s0 pc r sp ps m v).mem = m := rfl
@[simp] theorem mkS_pstate : (mkS s0 pc r sp ps m v).pstate = ps := rfl
@[simp] theorem mkS_status : (mkS s0 pc r sp ps m v).status = s0.status := rfl
@[simp] theorem mkS_spAligned : (mkS s0 pc r sp ps m v).spAligned = ((sp &&& 0b1111#64) == 0#64) := rfl

@[simp] theorem mkS_readGpr (i : BitVec 5) :
    (mkS s0 pc r sp ps m v).readReg64 (.gpr i) = if i = 31#5 then 0#64 else r i := by
  simp [mkS, State.readReg64, RegFile.read]
@[simp] theorem mkS_readSp : (mkS s0 pc r sp ps m v).readReg64 .sp = sp := rfl
@[simp] theorem mkS_readXzr : (mkS s0 pc r sp ps m v).readReg64 .xzr = 0#64 := rfl

@[simp] theorem mkS_writeGpr (i : BitVec 5) (x : BitVec 64) :
    (mkS s0 pc r sp ps m v).writeReg64 (.gpr i) x =
      mkS s0 pc (if i = 31#5 then r else upd r i x) sp ps m v := by
  by_cases h : i = 31#5
  · simp [mkS, State.writeReg64, h]
  · simp [mkS, State.writeReg64, h, RegFile.write]; rfl
@[simp] theorem mkS_writeSp (x : BitVec 64) :
    (mkS s0 pc r sp ps m v).writeReg64 .sp x = mkS s0 pc r x ps m v := rfl
@[simp] theorem mkS_writeXzr (x : BitVec 64) :
    (mkS s0 pc r sp ps m v).writeReg64 .xzr x = mkS s0 pc r sp ps m v := rfl

@[simp] theorem mkS_advancePC : (mkS s0 pc r sp ps m v).advancePC = mkS s0 (pc + 4#64) r sp ps m v := rfl
@[simp] theorem mkS_setPC (q : BitVec 64) : (mkS s0 pc r sp ps m v).setPC q = mkS s0 q r sp ps m v := rfl
@[simp] theorem mkS_setPState (q : PState) :
    (mkS s0 pc r sp ps m v).setPState q = mkS s0 pc r sp q m v := rfl
@[simp] theorem mkS_setMem (q : Memory) : (mkS s0 pc r sp ps m v).setMem q = mkS s0 pc r sp ps q v := rfl

@[simp] theorem mkS_readV (i : BitVec 5) : (mkS s0 pc r sp ps m v).readVReg128 i = v i := rfl
@[simp] theorem mkS_writeV (i : BitVec 5) (x : BitVec 128) :
    (mkS s0 pc r sp ps m v).writeVReg128 i x = mkS s0 pc r sp ps m (upd v i x) := by
  simp only [mkS, State.writeVReg128, VRegFile.write]; rfl

end

/-- Register reads of the entry state, as `mkS` sees them. -/
theorem readGpr_eq (s : State) (i : BitVec 5) (h : i ≠ 31#5) :
    s.readReg64 (.gpr i) = s.regs.regs i := by
  simp [State.readReg64, RegFile.read, h]

end Poly1305DebianCtFw

end
end

section
section
/-! # Execution by backward chaining, and instruction fetch in the placed libsodium library

`P pl ex` is the placed program with hook table `ex`. No hook has its entry point inside the text
block (`hook_none_in`), so inside the block `Step` is fetch-and-execute. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFw
open Poly1305DebianCt

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj

abbrev P (pl : Placement) (ex : String → Option (State → State)) : Program :=
  libsodiumDebianOnetimeauthCtLib.program pl ex

/-! ## Reaching a final state -/

theorem pc_add (b : BitVec 64) (k j : Nat) :
    b + BitVec.ofNat 64 k + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (k + j) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-! ## Code loaded, fetch -/

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
theorem code_length : libsodiumDebianOnetimeauthCtPlacedCode.length = 2324 := by rfl

theorem patched_length (pl : Placement) : (libsodiumDebianOnetimeauthCtText.patched pl).length = 2324 := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE]
  show (List.map (fun _ => 4) (List.range (libsodiumDebianOnetimeauthCtPlacedCode.length / 4))).sum = 2324
  rw [code_length]; rfl

theorem stub_far {pl : Placement} (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl) (e : String)
    (he : e ∈ libsodiumDebianOnetimeauthCtLib.text.externs) : 2324 ≤ (pl.ρ e - pl.base).toNat := by
  have := (hP.text.externs_ok e he).2
  rwa [show libsodiumDebianOnetimeauthCtLib.text.code.length = 2324 from code_length] at this

/-- No hook has its entry point inside the text block. -/
theorem hook_none_in {pl : Placement} (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    (ex : String → Option (State → State)) {off : Nat} (hoff : off < 2324) :
    (P pl ex).externAt? (pl.base + BitVec.ofNat 64 off) = none := by
  have e : (pl.base + BitVec.ofNat 64 off - pl.base).toNat = off := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  simp only [Program.externAt?, Program.hookAtOff?, P, PlacedLib.program, e]
  have h1 : (libsodiumDebianOnetimeauthCtLib.text.externs.map fun e => (e, (pl.ρ e - pl.base).toNat)).findSome?
      (fun (n, o) => if o == off then ex n else none) = none := by
    rw [List.findSome?_eq_none_iff]
    intro x hx
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
    have := stub_far hP e' he'
    have hne : ((pl.ρ e' - pl.base).toNat == off) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp only [hne, Bool.false_eq_true, ite_false]
  have h2 : libsodiumDebianOnetimeauthCtLib.text.symbols.findSome?
      (fun (n, o) => if o == off then (fun _ => (none : Option (State → State))) n else none) = none := by
    rw [List.findSome?_eq_none_iff]; intro x _; simp
  rw [h1]; simpa using h2

/-- Byte `k < 4` of the word at aligned offset `off` of the placed code. -/
theorem read8_code {pl : Placement} {ex : String → Option (State → State)} {m : Memory}
    (hCL : (P pl ex).CodeLoaded m) {off k : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 2324) (hk : k < 4) :
    m.read8 (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      (libsodiumDebianOnetimeauthCtText.patchedWord pl off).extractLsb' (8 * k) 8 ∧
    m.perm (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
  have hl : (P pl ex).code.length = 2324 := patched_length pl
  have h := codeLoaded_cell hCL (off + k) (by omega)
  have ha : pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
      (P pl ex).base + BitVec.ofNat 64 (off + k) := by
    show _ = pl.base + _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [ha]
  refine ⟨?_, h.2⟩
  rw [h.1]
  have ht := take4_drop_patched (blk := libsodiumDebianOnetimeauthCtText) (pl := pl) hal
    (by rw [show libsodiumDebianOnetimeauthCtText.code = libsodiumDebianOnetimeauthCtPlacedCode from rfl, code_length]; exact hlen)
  have e1 : (P pl ex).code[off + k]'(by omega) =
      (((libsodiumDebianOnetimeauthCtText.patched pl).drop off).take 4)[k]'(by
        simp [List.length_take, List.length_drop, patched_length]; omega) := by
    simp only [List.getElem_take, List.getElem_drop]; rfl
  rw [e1]
  simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * k + i < 32 := by omega
  simp [hi, this]; omega

theorem fetch_word {pl : Placement} {ex : String → Option (State → State)} {m : Memory}
    (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    (hCL : (P pl ex).CodeLoaded m) {off : Nat} (hal : off % 4 = 0) (hlen : off + 4 ≤ 2324) :
    (P pl ex).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      decode (libsodiumDebianOnetimeauthCtText.patchedWord pl off) := by
  have hb4 : pl.base.toNat % 4 = 0 := by
    have := hP.text.base_aligned
    simp [libsodiumDebianOnetimeauthCtLib, libsodiumDebianOnetimeauthCtText] at this; omega
  have hnw : pl.base.toNat + 2324 ≤ 2 ^ 64 := by
    have := hP.text.no_wrap
    have hl : libsodiumDebianOnetimeauthCtText.code.length = 2324 := code_length
    rw [show libsodiumDebianOnetimeauthCtLib.text = libsodiumDebianOnetimeauthCtText from rfl, hl] at this
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
  simp only [Program.fetchMem, hook_none_in hP ex (show off < 2324 by omega), Option.isSome_none,
    Bool.false_eq_true, if_false, hpc, ne_eq, not_true_eq_false]
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

theorem patchedWord_plain (pl : Placement) {off : Nat}
    (h : libsodiumDebianOnetimeauthCtText.relocAt? off = none) :
    libsodiumDebianOnetimeauthCtText.patchedWord pl off = libsodiumDebianOnetimeauthCtText.wordAt off := by
  simp [CodeBlock.patchedWord, h]

end Poly1305DebianCtFw

end
end

section
section
/-! # One lemma per instruction shape of `poly1305_finish`, on abstract states `mkS`

Some lemmas are copied from the x25519 `G` tree (`Solutions/X25519DalekField/G/Steps.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFw
open Poly1305DebianCt

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj

theorem awc_false_fst (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]
  omega

theorem awc_sub (x y : BitVec 64) : (AddWithCarry64 x (~~~y) true).1 = x - y := by
  simp only [AddWithCarry64, if_true]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have hx := x.isLt; have hy := y.isLt
  omega

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_stp64_pre_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hw1 : m.canWrite (sp + off) 8 = true)
    (hw2 : m.canWrite (sp + off + 8#64) 8 = true) :
    execInstWithSvc svc (.stp .W64 (.gpr a) (.gpr b) (.PreIndex .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r (sp + off) ps
        ((m.write64 (sp + off) (r a)).write64 (sp + off + 8#64) (r b)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hw1, hw2, ha, hb,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_stp64_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hw1 : m.canWrite (sp + off) 8 = true)
    (hw2 : m.canWrite (sp + off + 8#64) 8 = true) :
    execInstWithSvc svc (.stp .W64 (.gpr a) (.gpr b) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps ((m.write64 (sp + off) (r a)).write64 (sp + off + 8#64) (r b)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hw1, hw2, ha, hb,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_ldp64_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hr1 : m.canRead (sp + off) 8 = true)
    (hr2 : m.canRead (sp + off + 8#64) 8 = true) :
    execInstWithSvc svc (.ldp .W64 false (.gpr a) (.gpr b) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd (upd r a (m.read64 (sp + off))) b (m.read64 (sp + off + 8#64)))
        sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hr1, hr2, ha, hb,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_ldp64_post_sp (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hr1 : m.canRead sp 8 = true)
    (hr2 : m.canRead (sp + 8#64) 8 = true) :
    execInstWithSvc svc (.ldp .W64 false (.gpr a) (.gpr b) (.PostIndex .sp off))
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd (upd r a (m.read64 sp)) b (m.read64 (sp + 8#64)))
        (sp + off) ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hr1, hr2, ha, hb,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_ldr64_gpr (a n : BitVec 5) (ha : a ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hr : m.canRead (r n + off) 8 = true) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr a) (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r a (m.read64 (r n + off))) sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hr, ha, hn,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_strb_reg (t n k : BitVec 5) (ht : t ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (hw : m.canWrite (r n + r k) 1 = true) :
    execInstWithSvc svc (.str .B8 (.gpr t) (.RegOffset (.gpr n) (.gpr k) .UXTX 0))
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write8 (r n + r k) ((r t).truncate 8)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, extendVal, hw, ht, hn,
    hk, Memory.writeSized, AddrMode.baseReg]

theorem ex_mov (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W64 .ORR (.gpr d) .xzr (.gpr n) .LSL 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n)) sp ps m v := by
  simp [execInstWithSvc, execLogicalShift, evalLogical, State.readReg, State.writeReg, shiftVal,
    shift64, hd, hn]

theorem ex_add_gpr_sp (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .ADD (.gpr d) .sp imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (sp + imm.zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_false_fst, hd]

theorem ex_add_imm (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .ADD (.gpr d) (.gpr n) imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n + imm.zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, awc_false_fst, hd, hn]

theorem ex_cmp_imm (n : BitVec 5) (hn : n ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .SUBS .xzr (.gpr n) imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp (AddWithCarry64 (r n) (~~~(imm.zeroExtend 64)) true).2 m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, hn]

theorem ex_and_imm (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (mask : BitVec 64) :
    execInstWithSvc svc (.logicalImm .W64 .AND (.gpr d) (.gpr n) mask) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n &&& mask)) sp ps m v := by
  simp [execInstWithSvc, evalLogical, State.readReg, State.writeReg, hd, hn]

theorem ex_cbz (t : BitVec 5) (ht : t ≠ 31#5) (off : BitVec 64) :
    execInstWithSvc svc (.cbz .W64 false (.gpr t) off) (mkS s0 pc r sp ps m v) =
      mkS s0 (if r t = 0#64 then pc + off else pc + 4#64) r sp ps m v := by
  by_cases h : r t = 0#64 <;> simp [execInstWithSvc, State.readReg, ht, h]

theorem ex_bcond (c : CondCode) (off : BitVec 64) :
    execInstWithSvc svc (.bCond c off) (mkS s0 pc r sp ps m v) =
      mkS s0 (if ConditionHolds c ps then pc + off else pc + 4#64) r sp ps m v := by
  by_cases h : ConditionHolds c ps <;> simp [execInstWithSvc, h]

theorem ex_bl (off : BitVec 64) :
    execInstWithSvc svc (.bl off) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + off) (upd r 30#5 (pc + 4#64)) sp ps m v := by
  simp [execInstWithSvc]

theorem ex_b (off : BitVec 64) :
    execInstWithSvc svc (.b off) (mkS s0 pc r sp ps m v) = mkS s0 (pc + off) r sp ps m v := by
  simp [execInstWithSvc]

end exec

/-! ## Flags of `cmp` -/

theorem res_eq (x y : BitVec 64) : ((AddWithCarry64 x (~~~y) true).2.z) = decide (x = y) := by
  simp only [AddWithCarry64, if_true]
  have hx := x.isLt; have hy := y.isLt
  by_cases h : x = y
  · subst h; simp; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_not]; omega
  · simp only [h, decide_false, beq_eq_false_iff_ne]
    intro e; apply h; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat e
    simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_not] at this
    omega
theorem c_eq (x y : BitVec 64) : ((AddWithCarry64 x (~~~y) true).2.c) = decide (y.toNat ≤ x.toNat) := by
  simp only [AddWithCarry64, if_true]
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.msb_eq_decide]
  simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_not]
  omega
theorem hi_cmp (x y : BitVec 64) :
    ConditionHolds .HI (AddWithCarry64 x (~~~y) true).2 = decide (y.toNat < x.toNat) := by
  simp only [ConditionHolds, c_eq, res_eq]
  by_cases h : x = y
  · subst h; simp
  · have : x.toNat ≠ y.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp [h]; omega
theorem ne_cmp (x y : BitVec 64) :
    ConditionHolds .NE (AddWithCarry64 x (~~~y) true).2 = decide (x ≠ y) := by
  simp only [ConditionHolds, res_eq]; simp

end Poly1305DebianCtFw

end
end

section
section
/-! # 64-bit reads and writes inside owned byte lists; stack regions

`memRegion_split`, `memRegion_merge`, `pack64` and `unpack64_pack64` are copied from the x25519
`G` tree (`Solutions/X25519DalekField/G/Mem.lean`, `Solutions/X25519DalekEdwards/Dbl/Frame.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFw
open Poly1305DebianCt

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj Poly1305Boringssl

theorem memRegion_split (a : BitVec 64) (n k : Nat) (hnk : n + k < 2 ^ 64) :
    memRegion a (n + k) ⊢ memRegion a n ∗ memRegion (a + BitVec.ofNat 64 n) k := by
  intro h hh
  obtain ⟨bs, hb⟩ := memRegion_entails_bytes a (n + k) hnk h hh
  obtain ⟨hl, hb⟩ := pure_sepConj_holds.mp hb
  rw [pointsToBytes_split a bs n (by omega)] at hb
  have e1 : (bs.take n).length = n := by simp [hl]
  have e2 : (bs.drop n).length = k := by simp [hl]
  have m1 := bytes_entails_memRegion a (bs.take n)
  have m2 := bytes_entails_memRegion (a + BitVec.ofNat 64 n) (bs.drop n)
  rw [e1] at m1
  rw [e2] at m2
  exact sepConj_mono m1 m2 h hb

theorem memRegion_merge (a b : BitVec 64) (n k : Nat) (hb : b = a + BitVec.ofNat 64 n)
    (hn : n < 2 ^ 64) (hk : k < 2 ^ 64) :
    memRegion a n ∗ memRegion b k ⊢ memRegion a (n + k) := by
  subst hb
  intro h hh
  have h2 := sepConj_mono (memRegion_entails_bytes a n hn)
    (memRegion_entails_bytes (a + BitVec.ofNat 64 n) k hk) h hh
  rw [sepExists_sepConj] at h2
  obtain ⟨bs1, h2⟩ := h2
  dsimp only at h2
  rw [sepConj_comm, sepExists_sepConj] at h2
  obtain ⟨bs2, h2⟩ := h2
  dsimp only at h2
  have h3 : (⌜bs1.length = n⌝ ∗ ⌜bs2.length = k⌝ ∗ (a ↦ₛ bs1) ∗
      ((a + BitVec.ofNat 64 n) ↦ₛ bs2)).holds h := by
    have := Entails.of_eq (P := (⌜bs2.length = k⌝ ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bs2)) ∗
      (⌜bs1.length = n⌝ ∗ (a ↦ₛ bs1)))
      (Q := ⌜bs1.length = n⌝ ∗ ⌜bs2.length = k⌝ ∗ (a ↦ₛ bs1) ∗
      ((a + BitVec.ofNat 64 n) ↦ₛ bs2))
    exact this h h2
  obtain ⟨hl1, h3⟩ := pure_sepConj_holds.mp h3
  obtain ⟨hl2, h3⟩ := pure_sepConj_holds.mp h3
  have := bytes_entails_memRegion a (bs1 ++ bs2)
  rw [pointsToBytes_append, hl1, List.length_append, hl1, hl2] at this
  exact this h h3

def pack64 (l : List (BitVec 8)) : BitVec 64 :=
  l.getD 7 0 ++ l.getD 6 0 ++ l.getD 5 0 ++ l.getD 4 0 ++ l.getD 3 0 ++ l.getD 2 0 ++
    l.getD 1 0 ++ l.getD 0 0

theorem unpack64_pack64 (l : List (BitVec 8)) (h : l.length = 8) : unpack64 (pack64 l) = l := by
  match l, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    simp only [pack64, unpack64, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq,
      and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
      interval_cases i <;> simp

theorem app_toNat {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

theorem toNat_pack64 (l : List (BitVec 8)) (h : l.length = 8) :
    (pack64 l).toNat = leBytesToNum l := by
  match l, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    simp only [pack64, List.getD_cons_zero, List.getD_cons_succ, leBytesToNum, List.foldr_cons,
      List.foldr_nil, app_toNat]
    omega

end Poly1305DebianCtFw

end
end

section
section
/-! # More instruction shapes, small frames, and calling a function through its contract -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtFw
open Poly1305DebianCt

open Arm64 Arm64.Obj

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_hint (k : BitVec 7) :
    execInstWithSvc svc (.hint k) (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) r sp ps m v := by
  simp [execInstWithSvc]

theorem ex_nop :
    execInstWithSvc svc .nop (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) r sp ps m v := by
  simp [execInstWithSvc]

theorem ex_ret :
    execInstWithSvc svc (.ret (.gpr 30#5)) (mkS s0 pc r sp ps m v) =
      mkS s0 (r 30#5) r sp ps m v := by
  simp [execInstWithSvc]

theorem ex_ldrb_reg (t n k : BitVec 5) (ht : t ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (hr : m.canRead (r n + r k) 1 = true) :
    execInstWithSvc svc (.ldr .W32 .B8 false (.gpr t) (.RegOffset (.gpr n) (.gpr k) .UXTX 0))
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r t ((m.read8 (r n + r k)).zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, extendVal, hr, ht,
    hn, hk, Memory.readSized, AddrMode.baseReg, State.writeReg]

theorem ex_movz64 (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 16) :
    execInstWithSvc svc (.moveWide .W64 .MOVZ (.gpr d) imm 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (imm.zeroExtend 64)) sp ps m v := by
  simp [execInstWithSvc, execMoveWide, State.writeReg, hd]

theorem ex_sub_shift0 (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .SUB (.gpr d) (.gpr n) (.gpr k) .LSL 0)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n - r k)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, shiftVal, shift64, awc_sub,
    hd, hn, hk]

theorem ex_add_shift0 (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSL 0)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (r n + r k)) sp ps m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, shiftVal, shift64,
    awc_false_fst, hd, hn, hk]

theorem ex_cmp_reg (n k : BitVec 5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .SUBS .xzr (.gpr n) (.gpr k) .LSL 0)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp (AddWithCarry64 (r n) (~~~(r k)) true).2 m v := by
  simp [execInstWithSvc, evalAddSub, State.readReg, State.writeReg, shiftVal, shift64, hn, hk]

theorem ex_csel (c : CondCode) (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5)
    (hk : k ≠ 31#5) :
    execInstWithSvc svc (.condSelect .W64 .CSEL (.gpr d) (.gpr n) (.gpr k) c)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d (if ConditionHolds c ps = true then r n else r k)) sp ps m v := by
  by_cases h : ConditionHolds c ps = true <;>
    simp [execInstWithSvc, State.readReg, State.writeReg, hd, hn, hk, h]

theorem ex_str64_gpr (a n : BitVec 5) (ha : a ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hw : m.canWrite (r n + off) 8 = true) :
    execInstWithSvc svc (.str .X64 (.gpr a) (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write64 (r n + off) (r a)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hw, ha, hn,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_str64_xzr (n : BitVec 5) (hn : n ≠ 31#5) (off : BitVec 64)
    (hw : m.canWrite (r n + off) 8 = true) :
    execInstWithSvc svc (.str .X64 .xzr (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write64 (r n + off) 0#64) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hw, hn,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_str64_sp (a : BitVec 5) (ha : a ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hw : m.canWrite (sp + off) 8 = true) :
    execInstWithSvc svc (.str .X64 (.gpr a) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write64 (sp + off) (r a)) v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hw, ha,
    Memory.writeSized, AddrMode.baseReg]

theorem ex_ldr64_sp (a : BitVec 5) (ha : a ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hr : m.canRead (sp + off) 8 = true) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr a) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r a (m.read64 (sp + off))) sp ps m v := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hal, hr, ha,
    Memory.readSized, AddrMode.baseReg, State.writeReg]

end exec

theorem al16_iff (x : BitVec 64) : (x &&& 0b1111#64 = 0#64) ↔ x.toNat % 16 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and]
  have : (0b1111#64 : BitVec 64).toNat = 2 ^ 4 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem al16_sub (x : BitVec 64) (k : Nat) (hk : k % 16 = 0) (hk2 : k < 2 ^ 64)
    (h : x &&& 0b1111#64 = 0#64) : (x - BitVec.ofNat 64 k) &&& 0b1111#64 = 0#64 := by
  rw [al16_iff] at h ⊢
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk2]
  have := x.isLt
  omega

/-! ## Two-cell frames -/

theorem memRegion_eq_cells (a : BitVec 64) :
    memRegion a 16 ⊢ ∃∗ v0, ∃∗ v1, (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) := by
  intro h hh
  obtain ⟨bs, hb⟩ := memRegion_entails_bytes a 16 (by omega) h hh
  obtain ⟨hl, hb⟩ := pure_sepConj_holds.mp hb
  rw [pointsToBytes_split a bs 8 (by omega)] at hb
  refine ⟨pack64 (bs.take 8), pack64 (bs.drop 8), ?_⟩
  show ((a ↦₆₄ _) ∗ ((a + 8#64) ↦₆₄ _)).holds h
  rw [pointsTo64_eq_bytes, pointsTo64_eq_bytes, unpack64_pack64 _ (by simp [hl]),
    unpack64_pack64 _ (by simp [hl])]
  exact hb

theorem cells_entails_memRegion (a v0 v1 : BitVec 64) :
    ((a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1)) ⊢ memRegion a 16 := by
  rw [pointsTo64_eq_bytes, pointsTo64_eq_bytes]
  have := pointsToBytes_append a (unpack64 v0) (unpack64 v1)
  simp only [unpack64_length] at this
  rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← this]
  exact bytes_entails_memRegion a _

/-- The four saved cells of the 32-byte frame at `T`. -/
def Cells4 (T u0 u1 u2 u3 : BitVec 64) : SepProp :=
  (T ↦₆₄ u0) ∗ ((T + 8#64) ↦₆₄ u1) ∗ ((T + 0x10#64) ↦₆₄ u2) ∗ ((T + 0x10#64 + 8#64) ↦₆₄ u3)

theorem cells4_of_region {m : Memory} {T : BitVec 64} {F : SepProp}
    (h : m ⊨ memRegion T 32 ∗ F) : ∃ u0 u1 u2 u3, m ⊨ Cells4 T u0 u1 u2 u3 ∗ F := by
  have h1 := sat_sep_mono h (memRegion_split T 16 16 (by norm_num))
  rw [sepConj_assoc] at h1
  have h2 := sat_sep_mono h1 (memRegion_eq_cells T)
  rw [sepExists_sepConj, sat_sepExists] at h2
  obtain ⟨u0, h2⟩ := h2
  rw [sepExists_sepConj, sat_sepExists] at h2
  obtain ⟨u1, h2⟩ := h2
  have h3 := sat_sep_mono (Satisfies.of_eq h2 (Q := memRegion (T + BitVec.ofNat 64 16) 16 ∗
    (((T ↦₆₄ u0) ∗ ((T + 8#64) ↦₆₄ u1)) ∗ F))) (memRegion_eq_cells _)
  rw [sepExists_sepConj, sat_sepExists] at h3
  obtain ⟨u2, h3⟩ := h3
  rw [sepExists_sepConj, sat_sepExists] at h3
  obtain ⟨u3, h3⟩ := h3
  exact ⟨u0, u1, u2, u3, by simp only [Cells4]; exact Satisfies.of_eq h3⟩

theorem region_of_cells4 (T u0 u1 u2 u3 : BitVec 64) :
    Cells4 T u0 u1 u2 u3 ⊢ memRegion T 32 := by
  simp only [Cells4]
  have a1 := sepConj_mono (cells_entails_memRegion T u0 u1)
    (cells_entails_memRegion (T + 0x10#64) u2 u3)
  have a2 := memRegion_merge T (T + 0x10#64) 16 16 rfl (by norm_num) (by norm_num)
  refine Entails.trans (Entails.of_eq (by ac_rfl)) (Entails.trans a1 a2)

/-! ## Stepping, and calls -/

end Poly1305DebianCtFw

end
end

section
section
/-! # The instruction at each address of Debian's `poly1305_update` (text offsets 0x2b0..0x3a8)

Generated from `decode (wordAt off)`; `poly1305_update` has no relocations (its two `bl` go to
`poly1305_blocks` in the same object). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtUpdate
open Poly1305DebianCt

open Arm64 Arm64.Obj Poly1305DebianCtFw

section
variable {pl : Placement} {ex : String → Option (State → State)} {m : Memory}
  (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl) (hCL : (P pl ex).CodeLoaded m)
include hP hCL

theorem f_0 : (P pl ex).fetchMem m (pl.base + 688#64) = some (Arm64.Instr.hint 0x19#7) := by
  rw [show pl.base + 688#64 = pl.base + BitVec.ofNat 64 688 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_4 : (P pl ex).fetchMem m (pl.base + 692#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.sp) 0xffffffffffffffe0#64)) := by
  rw [show pl.base + 692#64 = pl.base + BitVec.ofNat 64 692 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_8 : (P pl ex).fetchMem m (pl.base + 696#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 696#64 = pl.base + BitVec.ofNat 64 696 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c : (P pl ex).fetchMem m (pl.base + 700#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 700#64 = pl.base + BitVec.ofNat 64 700 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_10 : (P pl ex).fetchMem m (pl.base + 704#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.sp) 0x000#12 false) := by
  rw [show pl.base + 704#64 = pl.base + BitVec.ofNat 64 704 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_14 : (P pl ex).fetchMem m (pl.base + 708#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x06#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000040#64)) := by
  rw [show pl.base + 708#64 = pl.base + BitVec.ofNat 64 708 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_18 : (P pl ex).fetchMem m (pl.base + 712#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x06#5) 0x0000000000000074#64) := by
  rw [show pl.base + 712#64 = pl.base + BitVec.ofNat 64 712 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_1c : (P pl ex).fetchMem m (pl.base + 716#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x01#5) 0x0010#16 0) := by
  rw [show pl.base + 716#64 = pl.base + BitVec.ofNat 64 716 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_20 : (P pl ex).fetchMem m (pl.base + 720#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x06#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 720#64 = pl.base + BitVec.ofNat 64 720 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_24 : (P pl ex).fetchMem m (pl.base + 724#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 724#64 = pl.base + BitVec.ofNat 64 724 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_28 : (P pl ex).fetchMem m (pl.base + 728#64) = some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSEL) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x02#5) (Arm64.CondCode.LS)) := by
  rw [show pl.base + 728#64 = pl.base + BitVec.ofNat 64 728 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_2c : (P pl ex).fetchMem m (pl.base + 732#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x01#5) 0x0000000000000024#64) := by
  rw [show pl.base + 732#64 = pl.base + BitVec.ofNat 64 732 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_30 : (P pl ex).fetchMem m (pl.base + 736#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x06#5) 0x048#12 false) := by
  rw [show pl.base + 736#64 = pl.base + BitVec.ofNat 64 736 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_34 : (P pl ex).fetchMem m (pl.base + 740#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x03#5) 0x0000#16 0) := by
  rw [show pl.base + 740#64 = pl.base + BitVec.ofNat 64 740 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_38 : (P pl ex).fetchMem m (pl.base + 744#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x05#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 744#64 = pl.base + BitVec.ofNat 64 744 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_3c : (P pl ex).fetchMem m (pl.base + 748#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x02#5) (Arm64.AddrMode.RegOffset (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ExtendType.UXTX) 0)) := by
  rw [show pl.base + 748#64 = pl.base + BitVec.ofNat 64 748 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_40 : (P pl ex).fetchMem m (pl.base + 752#64) = some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x02#5) (Arm64.AddrMode.RegOffset (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ExtendType.UXTX) 0)) := by
  rw [show pl.base + 752#64 = pl.base + BitVec.ofNat 64 752 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_44 : (P pl ex).fetchMem m (pl.base + 756#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) 0x001#12 false) := by
  rw [show pl.base + 756#64 = pl.base + BitVec.ofNat 64 756 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_48 : (P pl ex).fetchMem m (pl.base + 760#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 760#64 = pl.base + BitVec.ofNat 64 760 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_4c : (P pl ex).fetchMem m (pl.base + 764#64) = some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0xfffffffffffffff0#64) := by
  rw [show pl.base + 764#64 = pl.base + BitVec.ofNat 64 764 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_50 : (P pl ex).fetchMem m (pl.base + 768#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 768#64 = pl.base + BitVec.ofNat 64 768 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_54 : (P pl ex).fetchMem m (pl.base + 772#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x06#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000040#64)) := by
  rw [show pl.base + 772#64 = pl.base + BitVec.ofNat 64 772 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_58 : (P pl ex).fetchMem m (pl.base + 776#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x06#5) 0x00f#12 false) := by
  rw [show pl.base + 776#64 = pl.base + BitVec.ofNat 64 776 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_5c : (P pl ex).fetchMem m (pl.base + 780#64) = some (Arm64.Instr.bCond (Arm64.CondCode.HI) 0x0000000000000010#64) := by
  rw [show pl.base + 780#64 = pl.base + BitVec.ofNat 64 780 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_60 : (P pl ex).fetchMem m (pl.base + 784#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.sp) 0x0000000000000020#64)) := by
  rw [show pl.base + 784#64 = pl.base + BitVec.ofNat 64 784 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_64 : (P pl ex).fetchMem m (pl.base + 788#64) = some (Arm64.Instr.hint 0x1d#7) := by
  rw [show pl.base + 788#64 = pl.base + BitVec.ofNat 64 788 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_68 : (P pl ex).fetchMem m (pl.base + 792#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) := by
  rw [show pl.base + 792#64 = pl.base + BitVec.ofNat 64 792 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_6c : (P pl ex).fetchMem m (pl.base + 796#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 796#64 = pl.base + BitVec.ofNat 64 796 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_70 : (P pl ex).fetchMem m (pl.base + 800#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 800#64 = pl.base + BitVec.ofNat 64 800 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_74 : (P pl ex).fetchMem m (pl.base + 804#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x02#5) 0x0010#16 0) := by
  rw [show pl.base + 804#64 = pl.base + BitVec.ofNat 64 804 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_78 : (P pl ex).fetchMem m (pl.base + 808#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x00#5) 0x048#12 false) := by
  rw [show pl.base + 808#64 = pl.base + BitVec.ofNat 64 808 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_7c : (P pl ex).fetchMem m (pl.base + 812#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) := by
  rw [show pl.base + 812#64 = pl.base + BitVec.ofNat 64 812 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_80 : (P pl ex).fetchMem m (pl.base + 816#64) = some (Arm64.Instr.bl 0xfffffffffffffe70#64) := by
  rw [show pl.base + 816#64 = pl.base + BitVec.ofNat 64 816 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_84 : (P pl ex).fetchMem m (pl.base + 820#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.xzr) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000040#64)) := by
  rw [show pl.base + 820#64 = pl.base + BitVec.ofNat 64 820 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_88 : (P pl ex).fetchMem m (pl.base + 824#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) := by
  rw [show pl.base + 824#64 = pl.base + BitVec.ofNat 64 824 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_8c : (P pl ex).fetchMem m (pl.base + 828#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x04#5) 0x00f#12 false) := by
  rw [show pl.base + 828#64 = pl.base + BitVec.ofNat 64 828 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_90 : (P pl ex).fetchMem m (pl.base + 832#64) = some (Arm64.Instr.bCond (Arm64.CondCode.HI) 0x0000000000000048#64) := by
  rw [show pl.base + 832#64 = pl.base + BitVec.ofNat 64 832 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_94 : (P pl ex).fetchMem m (pl.base + 836#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x04#5) 0xffffffffffffffcc#64) := by
  rw [show pl.base + 836#64 = pl.base + BitVec.ofNat 64 836 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_98 : (P pl ex).fetchMem m (pl.base + 840#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x05#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000040#64)) := by
  rw [show pl.base + 840#64 = pl.base + BitVec.ofNat 64 840 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_9c : (P pl ex).fetchMem m (pl.base + 844#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x03#5) 0x0000#16 0) := by
  rw [show pl.base + 844#64 = pl.base + BitVec.ofNat 64 844 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a0 : (P pl ex).fetchMem m (pl.base + 848#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x05#5) 0x048#12 false) := by
  rw [show pl.base + 848#64 = pl.base + BitVec.ofNat 64 848 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a4 : (P pl ex).fetchMem m (pl.base + 852#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 852#64 = pl.base + BitVec.ofNat 64 852 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_a8 : (P pl ex).fetchMem m (pl.base + 856#64) = some (Arm64.Instr.nop) := by
  rw [show pl.base + 856#64 = pl.base + BitVec.ofNat 64 856 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_ac : (P pl ex).fetchMem m (pl.base + 860#64) = some (Arm64.Instr.nop) := by
  rw [show pl.base + 860#64 = pl.base + BitVec.ofNat 64 860 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b0 : (P pl ex).fetchMem m (pl.base + 864#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.RegOffset (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ExtendType.UXTX) 0)) := by
  rw [show pl.base + 864#64 = pl.base + BitVec.ofNat 64 864 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b4 : (P pl ex).fetchMem m (pl.base + 868#64) = some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.RegOffset (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ExtendType.UXTX) 0)) := by
  rw [show pl.base + 868#64 = pl.base + BitVec.ofNat 64 868 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_b8 : (P pl ex).fetchMem m (pl.base + 872#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) 0x001#12 false) := by
  rw [show pl.base + 872#64 = pl.base + BitVec.ofNat 64 872 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_bc : (P pl ex).fetchMem m (pl.base + 876#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 876#64 = pl.base + BitVec.ofNat 64 876 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c0 : (P pl ex).fetchMem m (pl.base + 880#64) = some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0xfffffffffffffff0#64) := by
  rw [show pl.base + 880#64 = pl.base + BitVec.ofNat 64 880 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c4 : (P pl ex).fetchMem m (pl.base + 884#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x04#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 884#64 = pl.base + BitVec.ofNat 64 884 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_c8 : (P pl ex).fetchMem m (pl.base + 888#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x05#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000040#64)) := by
  rw [show pl.base + 888#64 = pl.base + BitVec.ofNat 64 888 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_cc : (P pl ex).fetchMem m (pl.base + 892#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.sp) 0x0000000000000020#64)) := by
  rw [show pl.base + 892#64 = pl.base + BitVec.ofNat 64 892 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d0 : (P pl ex).fetchMem m (pl.base + 896#64) = some (Arm64.Instr.hint 0x1d#7) := by
  rw [show pl.base + 896#64 = pl.base + BitVec.ofNat 64 896 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d4 : (P pl ex).fetchMem m (pl.base + 900#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) := by
  rw [show pl.base + 900#64 = pl.base + BitVec.ofNat 64 900 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_d8 : (P pl ex).fetchMem m (pl.base + 904#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x04#5) 0xfffffffffffffff0#64) := by
  rw [show pl.base + 904#64 = pl.base + BitVec.ofNat 64 904 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_dc : (P pl ex).fetchMem m (pl.base + 908#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x12#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 908#64 = pl.base + BitVec.ofNat 64 908 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e0 : (P pl ex).fetchMem m (pl.base + 912#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) := by
  rw [show pl.base + 912#64 = pl.base + BitVec.ofNat 64 912 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e4 : (P pl ex).fetchMem m (pl.base + 916#64) = some (Arm64.Instr.bl 0xfffffffffffffe0c#64) := by
  rw [show pl.base + 916#64 = pl.base + BitVec.ofNat 64 916 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_e8 : (P pl ex).fetchMem m (pl.base + 920#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) := by
  rw [show pl.base + 920#64 = pl.base + BitVec.ofNat 64 920 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_ec : (P pl ex).fetchMem m (pl.base + 924#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 924#64 = pl.base + BitVec.ofNat 64 924 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f0 : (P pl ex).fetchMem m (pl.base + 928#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) := by
  rw [show pl.base + 928#64 = pl.base + BitVec.ofNat 64 928 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f4 : (P pl ex).fetchMem m (pl.base + 932#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x04#5) 0xffffffffffffff6c#64) := by
  rw [show pl.base + 932#64 = pl.base + BitVec.ofNat 64 932 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

theorem f_f8 : (P pl ex).fetchMem m (pl.base + 936#64) = some (Arm64.Instr.b 0xffffffffffffffa0#64) := by
  rw [show pl.base + 936#64 = pl.base + BitVec.ofNat 64 936 from rfl,
    fetch_word hP hCL (by decide) (by decide), patchedWord_plain pl (by rfl)]; rfl

end

end Poly1305DebianCtUpdate

end
end

section
section
/-! # Two runs of `poly1305_update` in lock step: the step rules, the memory layout, the call

States are `Poly1305DebianCtFw.mkS c pc r sp ps m c.vregs.regs` over each run's entry state `c`.
`rs` steps both runs by one instruction given the execution equations (`ex_…` lemmas); `rsw` also
hands the continuation the loaded code of the new memories (after a store). `call2` is the
`bl poly1305_blocks` of both runs, through `blocks_rel_sep'` (a copy of
`Poly1305DebianCtBlocks.blocks_rel_sep` that also returns the loaded code). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtUpdate

open Arm64 Arm64.Obj Poly1305DebianCt Leakage Poly1305DebianCtFw Poly1305Boringssl
open Poly1305Libsodium (u64At bytesIn)

/-! ## Arithmetic and byte lists -/

theorem pc4 (b : BitVec 64) (x y : Nat) (h : x + 4 = y := by decide) :
    b + BitVec.ofNat 64 x + 4#64 = b + BitVec.ofNat 64 y := by
  rw [pc_add, h]

theorem leBytesToNum_unpack64 (v : BitVec 64) : leBytesToNum (unpack64 v) = v.toNat := by
  have h := v.isLt
  simp only [unpack64, leBytesToNum, List.foldr_cons, List.foldr_nil, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  generalize v.toNat = x at h ⊢
  norm_num at h ⊢
  omega

theorem split96 (st : List (BitVec 8)) (h : st.length = 96) :
    st = st.take 48 ++ (st.drop 48).take 16 ++ (st.drop 64).take 8 ++ (st.drop 72).take 16 ++
      st.getD 88 0#8 :: st.drop 89 := by
  have d1 : (st.drop 48).take 16 ++ st.drop 64 = st.drop 48 := by
    have := List.take_append_drop 16 (st.drop 48)
    rw [List.drop_drop] at this; simpa using this
  have d2 : (st.drop 64).take 8 ++ st.drop 72 = st.drop 64 := by
    have := List.take_append_drop 8 (st.drop 64)
    rw [List.drop_drop] at this; simpa using this
  have d3 : (st.drop 72).take 16 ++ st.drop 88 = st.drop 72 := by
    have := List.take_append_drop 16 (st.drop 72)
    rw [List.drop_drop] at this; simpa using this
  have h88 : 88 < st.length := by omega
  have d4 : st.getD 88 0#8 :: st.drop 89 = st.drop 88 := by
    rw [List.drop_eq_getElem_cons h88]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h88]
  symm
  simp only [List.append_assoc]
  rw [d4, d3, d2, d1, List.take_append_drop]

/-- The 8 bytes at 64 of the state assembled from its fields. -/
theorem u64At_fields (rh pad w buf rest : List (BitVec 8)) (fin : BitVec 8)
    (h1 : rh.length = 48) (h2 : pad.length = 16) (h3 : w.length = 8) :
    u64At (rh ++ pad ++ w ++ buf ++ fin :: rest) 64 = leBytesToNum w := by
  unfold u64At
  simp only [List.append_assoc]
  rw [show 64 = 48 + 16 from rfl, ← List.drop_drop, List.drop_left' h1, List.drop_left' h2,
    List.take_left' h3]

/-- The 96 state bytes at `a` as fields: `buffer` (16 at 72), `leftover` (a cell at 64), `r,h`
(48), `final` (one byte at 88), `pad` (16 at 48), the rest (7 from 89). -/
def Fields (a : BitVec 64) (rh pad : List (BitVec 8)) (lo : BitVec 64) (buf : List (BitVec 8))
    (fin : BitVec 8) (rest : List (BitVec 8)) : SepProp :=
  ((a + 72#64) ↦ₛ buf) ∗ ((a + 64#64) ↦₆₄ lo) ∗ (a ↦ₛ rh) ∗ ((a + 88#64) ↦ₛ [fin]) ∗
    ((a + 48#64) ↦ₛ pad) ∗ ((a + 89#64) ↦ₛ rest)

theorem fields_eq (a : BitVec 64) (rh pad buf rest : List (BitVec 8)) (lo : BitVec 64)
    (fin : BitVec 8) (h1 : rh.length = 48) (h2 : pad.length = 16) (h4 : buf.length = 16) :
    (a ↦ₛ (rh ++ pad ++ unpack64 lo ++ buf ++ fin :: rest)) = Fields a rh pad lo buf fin rest := by
  simp only [List.append_assoc, Fields]
  rw [show fin :: rest = [fin] ++ rest from rfl, pointsToBytes_append, pointsToBytes_append,
    pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, ← pointsTo64_eq_bytes]
  simp only [h1, h2, h4, unpack64_length, List.length_singleton, pc_add, Nat.reduceAdd]
  ac_rfl

theorem bytesIn_split (ro : Bool) (p : BitVec 64) (I : List (BitVec 8)) (k : Nat)
    (hk : k ≤ I.length) :
    bytesIn ro p I = bytesIn ro p (I.take k) ∗ bytesIn ro (p + BitVec.ofNat 64 k) (I.drop k) := by
  cases ro
  · simp only [bytesIn, Bool.false_eq_true, ↓reduceIte]; exact pointsToBytes_split p I k hk
  · simp only [bytesIn, ↓reduceIte]; exact pointsToBytesRO_split p I k hk

theorem bytesIn_three (ro : Bool) (p : BitVec 64) (msg : List (BitVec 8)) (j B : Nat)
    (h : j + B ≤ msg.length) :
    bytesIn ro p msg = bytesIn ro p (msg.take j) ∗
      (bytesIn ro (p + BitVec.ofNat 64 j) ((msg.drop j).take B) ∗
        bytesIn ro (p + BitVec.ofNat 64 j + BitVec.ofNat 64 B) ((msg.drop j).drop B)) := by
  rw [bytesIn_split ro p msg j (by omega),
    bytesIn_split ro (p + BitVec.ofNat 64 j) (msg.drop j) B (by simp; omega)]

theorem and_mask_hi (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n &&& 0xfffffffffffffff0#64) = BitVec.ofNat 64 (16 * (n / 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,
    show (0xfffffffffffffff0#64 : BitVec 64).toNat = 2 ^ 4 * (2 ^ 60 - 1) + 0 from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega)]
  have hq : n / 16 < 2 ^ 60 := by omega
  have e : n = 2 ^ 4 * (n / 16) + n % 16 := by omega
  rw [show 16 * (n / 16) = 2 ^ 4 * (n / 16) + 0 by omega]
  conv_lhs => rw [e]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ (by omega),
    Nat.testBit_two_pow_mul_add _ (by norm_num), Nat.testBit_two_pow_mul_add _ (by norm_num)]
  split
  · simp
  · rw [Nat.testBit_two_pow_sub_one]
    by_cases h : i - 4 < 60
    · simp [h]
    · simp only [h, decide_false, Bool.and_false]
      symm
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem ofNat_sub_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega

theorem ofNat_eq_zero (k : Nat) (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k = 0#64) ↔ k = 0 := by
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    simp at this
    omega
  · rintro rfl; rfl

theorem hi15 (x : BitVec 64) :
    ConditionHolds .HI (AddWithCarry64 x (~~~((0x00f#12 : BitVec 12).zeroExtend 64)) true).2 =
      decide (15 < x.toNat) := by
  rw [hi_cmp]; rfl

theorem ls_cmp (x y : BitVec 64) :
    ConditionHolds .LS (AddWithCarry64 x (~~~y) true).2 = decide (x.toNat ≤ y.toNat) := by
  simp only [ConditionHolds, c_eq, res_eq]
  rcases Nat.lt_or_ge x.toNat y.toNat with h | h
  · have h1 : ¬ y.toNat ≤ x.toNat := by omega
    simp [h1, Nat.le_of_lt h]
  · by_cases he : x = y
    · subst he; simp
    · have hlt : y.toNat < x.toNat :=
        lt_of_le_of_ne h (fun e => he (BitVec.eq_of_toNat_eq e.symm))
      have h2 : ¬ x.toNat ≤ y.toNat := by omega
      simp [h, he, h2]

theorem src_byte {m : Memory} {ro : Bool} {P : BitVec 64} {S : List (BitVec 8)} {G : SepProp}
    (hm : m ⊨ bytesIn ro P S ∗ G) (i : Nat) (hi : i < S.length) :
    m.canRead (P + BitVec.ofNat 64 i) 1 = true := by
  have e : ∀ n, n < 1 → P + BitVec.ofNat 64 i + BitVec.ofNat 64 n = P + BitVec.ofNat 64 i := by
    intro n hn
    rw [show n = 0 by omega]
    simp
  cases ro
  · simp only [bytesIn, Bool.false_eq_true, ↓reduceIte] at hm
    have H := sat_bytes_read hm i hi
    refine canRead_of (fun n hn => ?_)
    rw [e n hn, H.2.1]
    exact ⟨rfl, H.2.2⟩
  · simp only [bytesIn, ↓reduceIte] at hm
    have H := sat_bytesRO_read hm i hi
    refine canRead_of (fun n hn => ?_)
    rw [e n hn]
    exact H.2

theorem dst_byte {m : Memory} {A : BitVec 64} {D : List (BitVec 8)} {G : SepProp}
    (hm : m ⊨ (A ↦ₛ D) ∗ G) (j : Nat) (hj : j < D.length) :
    m.canWrite (A + BitVec.ofNat 64 j) 1 = true := by
  have H := sat_bytes_read hm j hj
  refine canWrite_of (fun n hn => ?_)
  rw [show n = 0 by omega]
  simpa using H.2.1

theorem ofNat_succ (i : Nat) : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.ofNat_add]

theorem ne_ofNat_iff (c i : Nat) (hc : c < 2 ^ 64) (hi : i ≤ c) :
    (BitVec.ofNat 64 c ≠ BitVec.ofNat 64 i) ↔ c ≠ i := by
  constructor
  · intro h e; exact h (by rw [e])
  · intro h e
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt (by omega)] at this
    exact h this

/-! ## Registers kept -/

/-- Registers `x19`..`x31` other than `x29`, `x30` as in `r0`. -/
def Kept (r r0 : BitVec 5 → BitVec 64) : Prop :=
  ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat ≠ 29 → k.toNat ≠ 30 → r k = r0 k

theorem Kept.upd {r r0 : BitVec 5 → BitVec 64} (h : Kept r r0) (i : BitVec 5)
    (hi : i.toNat < 19 ∨ i.toNat = 29 ∨ i.toNat = 30) (x : BitVec 64) :
    Kept (Poly1305DebianCtFw.upd r i x) r0 := by
  intro k h1 h2 h3
  rw [upd_ne _ _ (by rintro rfl; omega)]
  exact h k h1 h2 h3

theorem Kept.mkRegs {r r0 : BitVec 5 → BitVec 64} (h : Kept r r0) (q : Nat → BitVec 64) :
    Kept (Poly1305DebianCtBlocks.mkRegs ⟨r⟩ q).regs r0 := by
  intro k h1 h2 h3
  simp only [Poly1305DebianCtBlocks.mkRegs]
  rw [if_neg (by omega)]
  exact h k h1 h2 h3

theorem mkRegs_out (r : BitVec 5 → BitVec 64) (q : Nat → BitVec 64) (k : BitVec 5)
    (h : k.toNat = 0 ∨ 18 ≤ k.toNat) : (Poly1305DebianCtBlocks.mkRegs ⟨r⟩ q).regs k = r k := by
  simp only [Poly1305DebianCtBlocks.mkRegs]
  rw [if_neg (by omega)]

/-! ## Each run's data and memory -/

/-- What a run carries besides its entry state: the message (and whether it is read-only), the
untouched state fields (`pad`, `final`, the last 7 bytes), and the caller's frame. -/
structure RunD where
  ro : Bool
  msg : List (BitVec 8)
  pad : List (BitVec 8)
  rest : List (BitVec 8)
  fin : BitVec 8
  R : SepProp

/-- A run's memory after the prologue: the state fields at `a` (leftover cell `lo`), the message
at `p`, the 32-byte frame at `T` (saved `x29`, `x30` of `c`, and two spill slots), the frame. -/
def Mem (c : State) (d : RunD) (a p T lo : BitVec 64) (rh buf : List (BitVec 8))
    (u2 u3 : BitVec 64) : SepProp :=
  Fields a rh d.pad lo buf d.fin d.rest ∗ bytesIn d.ro p d.msg ∗
    Cells4 T (c.regs.regs 29#5) (c.regs.regs 30#5) u2 u3 ∗ d.R

section rel

variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

/-- One instruction in both runs, given its execution equations. -/
theorem rs (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State} (hr₁ : c₁.status = .Running)
    (hr₂ : c₂.status = .Running) {pc sp : BitVec 64} {r₁ r₂ : BitVec 5 → BitVec 64}
    {ps₁ ps₂ : PState} {m₁ m₂ : Memory} {v₁ v₂ : BitVec 5 → BitVec 128} {i : Instr} {t₁ t₂ : State}
    (hf1 : (P pl X).fetchMem m₁ pc = some i) (hf2 : (P pl X).fetchMem m₂ pc = some i)
    (e1 : execInstWithSvc (evalSvc (P pl X).svc) i (mkS c₁ pc r₁ sp ps₁ m₁ v₁) = t₁)
    (e2 : execInstWithSvc (evalSvc (P pl X).svc) i (mkS c₂ pc r₂ sp ps₂ m₂ v₂) = t₂)
    (hl : leakedValues i (mkS c₁ pc r₁ sp ps₁ m₁ v₁) = leakedValues i (mkS c₂ pc r₂ sp ps₂ m₂ v₂))
    (h : ObsEquiv (P pl X) arity stop₁ stop₂ t₁ t₂) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pc r₁ sp ps₁ m₁ v₁) (mkS c₂ pc r₂ sp ps₂ m₂ v₂) := by
  subst e1 e2
  exact oe_exec hc rfl rfl hr₁ hr₂ hf1 hf2 hl h

/-- `rs`, handing the continuation the loaded code of the new memories. -/
theorem rsw (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State} (hr₁ : c₁.status = .Running)
    (hr₂ : c₂.status = .Running) {pc sp : BitVec 64} {r₁ r₂ : BitVec 5 → BitVec 64}
    {ps₁ ps₂ : PState} {m₁ m₂ : Memory} {v₁ v₂ : BitVec 5 → BitVec 128} {i : Instr} {t₁ t₂ : State}
    (hcl₁ : (P pl X).CodeLoaded m₁) (hcl₂ : (P pl X).CodeLoaded m₂)
    (hf1 : (P pl X).fetchMem m₁ pc = some i) (hf2 : (P pl X).fetchMem m₂ pc = some i)
    (e1 : execInstWithSvc (evalSvc (P pl X).svc) i (mkS c₁ pc r₁ sp ps₁ m₁ v₁) = t₁)
    (e2 : execInstWithSvc (evalSvc (P pl X).svc) i (mkS c₂ pc r₂ sp ps₂ m₂ v₂) = t₂)
    (hl : leakedValues i (mkS c₁ pc r₁ sp ps₁ m₁ v₁) = leakedValues i (mkS c₂ pc r₂ sp ps₂ m₂ v₂))
    (h : (P pl X).CodeLoaded t₁.mem → (P pl X).CodeLoaded t₂.mem →
      ObsEquiv (P pl X) arity stop₁ stop₂ t₁ t₂) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pc r₁ sp ps₁ m₁ v₁) (mkS c₂ pc r₂ sp ps₂ m₂ v₂) := by
  have s1 : Step (P pl X) (mkS c₁ pc r₁ sp ps₁ m₁ v₁) t₁ := e1 ▸ Step.exec hr₁ hf1
  have s2 : Step (P pl X) (mkS c₂ pc r₂ sp ps₂ m₂ v₂) t₂ := e2 ▸ Step.exec hr₂ hf2
  have k1 := Arm64Facts.steps_codeLoaded_v2 (Steps.step s1 (Steps.refl _)) hcl₁
  have k2 := Arm64Facts.steps_codeLoaded_v2 (Steps.step s2 (Steps.refl _)) hcl₂
  exact rs hc hr₁ hr₂ hf1 hf2 e1 e2 hl (h k1 k2)

end rel

/-! ## Calling `poly1305_blocks` -/

/-- `Poly1305DebianCtBlocks.blocks_rel_sep`, with the loaded code of the return memories. -/
theorem blocks_rel_sep' {pl : Placement} {X : String → Option (State → State)}
    {stop₁ stop₂ : State → Prop} (hc : StopCompat stop₁ stop₂)
    (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl) {c₁ c₂ : State}
    (hrun₁ : c₁.status = .Running) (hrun₂ : c₂.status = .Running)
    (hpc₁ : c₁.pc = pl.base + 416#64) (hpc₂ : c₂.pc = pl.base + 416#64)
    (hcl₁ : (Poly1305DebianCtBlocks.prog pl X).CodeLoaded c₁.mem)
    (hcl₂ : (Poly1305DebianCtBlocks.prog pl X).CodeLoaded c₂.mem)
    (hsp : c₁.sp = c₂.sp) (hX0 : Poly1305DebianCtBlocks.X0 c₁ = Poly1305DebianCtBlocks.X0 c₂)
    (hx1 : c₁.readReg64 (.gpr 1#5) = c₂.readReg64 (.gpr 1#5))
    (hx2 : c₁.readReg64 (.gpr 2#5) = c₂.readReg64 (.gpr 2#5))
    {F₁ F₂ : SepProp} {ro₁ ro₂ : Bool} {rh₁ rh₂ : List (BitVec 8)} {fin₁ fin₂ : BitVec 8}
    {msg₁ msg₂ : List (BitVec 8)}
    (hpre₁ : c₁.mem ⊨ blocksPre pl (ro₁, rh₁, fin₁, msg₁) c₁ ∗ F₁)
    (hpre₂ : c₂.mem ⊨ blocksPre pl (ro₂, rh₂, fin₂, msg₂) c₂ ∗ F₂)
    (K : ∀ (m₁ m₂ : Memory) (ps₁ ps₂ : PState) (r₁ r₂ : Nat → BitVec 64) (rh₁' rh₂' : List (BitVec 8)),
      (Poly1305DebianCtBlocks.prog pl X).CodeLoaded m₁ →
      (Poly1305DebianCtBlocks.prog pl X).CodeLoaded m₂ →
      (m₁ ⊨ blocksPre pl (ro₁, rh₁', fin₁, msg₁) c₁ ∗ F₁) →
      (m₂ ⊨ blocksPre pl (ro₂, rh₂', fin₂, msg₂) c₂ ∗ F₂) →
      ObsEquiv (Poly1305DebianCtBlocks.prog pl X) arity stop₁ stop₂
        (Poly1305DebianCtBlocks.mkS c₁ (c₁.readReg64 (.gpr 0x1e#5)) c₁.sp m₁ ps₁ r₁)
        (Poly1305DebianCtBlocks.mkS c₂ (c₂.readReg64 (.gpr 0x1e#5)) c₂.sp m₂ ps₂ r₂)) :
    ObsEquiv (Poly1305DebianCtBlocks.prog pl X) arity stop₁ stop₂ c₁ c₂ := by
  obtain ⟨F₁', hlen₁, h16, h16d, hmsg₁⟩ := Poly1305DebianCtBlocks.ctfacts_of_pre (X := X) hP hcl₁ hpre₁
  obtain ⟨F₂', hlen₂, -, -, hmsg₂⟩ := Poly1305DebianCtBlocks.ctfacts_of_pre (X := X) hP hcl₂ hpre₂
  have hl₂ : msg₂.length = msg₁.length := by rw [← hlen₁, ← hlen₂, hx2]
  rw [hl₂, ← hx1] at hmsg₂
  rw [← hlen₁] at h16 h16d hmsg₁ hmsg₂
  refine Poly1305DebianCtBlocks.blocks_rel hc hrun₁ hrun₂ hpc₁ hpc₂ F₁' F₂' hsp hX0 hx1 hx2 h16 h16d
    hmsg₁ hmsg₂ ?_
  intro m₁ m₂ ps₁ ps₂ r₁ r₂ ok₁ ok₂
  obtain ⟨rh₁', h₁⟩ := Poly1305DebianCtBlocks.post_of_memOk hpre₁ ok₁
  obtain ⟨rh₂', h₂⟩ := Poly1305DebianCtBlocks.post_of_memOk hpre₂ ok₂
  exact K m₁ m₂ ps₁ ps₂ r₁ r₂ rh₁' rh₂' (Poly1305DebianCtBlocks.Good.codeLoaded ⟨hP, hcl₁, ok₁⟩)
    (Poly1305DebianCtBlocks.Good.codeLoaded ⟨hP, hcl₂, ok₂⟩) h₁ h₂

theorem blocksPre_mkS {pl : Placement} {c : State} {pc T : BitVec 64} {r : BitVec 5 → BitVec 64}
    {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {ro : Bool} {rh msg : List (BitVec 8)}
    {fin : BitVec 8} {F : SepProp} :
    blocksPre pl (ro, rh, fin, msg) (mkS c pc r T ps m v) ∗ F =
      ⌜rh.length = 48 ∧ (r 2#5).toNat = msg.length ∧ 16 ≤ msg.length ∧ msg.length % 16 = 0⌝ ∗
        ((r 0#5 ↦ₛ rh) ∗ ((r 0#5 + 88#64) ↦ₛ [fin]) ∗ bytesIn ro (r 1#5) msg ∗ F) := by
  simp only [blocksPre, mkS_readGpr, Reg.x0, Reg.x1, Reg.x2]
  simp only [show (0#5 : BitVec 5) = 31#5 ↔ False by decide,
    show (1#5 : BitVec 5) = 31#5 ↔ False by decide, show (2#5 : BitVec 5) = 31#5 ↔ False by decide,
    if_false]
  simp only [sepConj_assoc]

/-- The state `poly1305_blocks` returns, as an abstract state over the caller's entry `c`. -/
theorem ret_eq (c : State) (pcB pc T : BitVec 64) (R : BitVec 5 → BitVec 64) (ps0 ps : PState)
    (m0 m : Memory) (v : BitVec 5 → BitVec 128) (q : Nat → BitVec 64) :
    Poly1305DebianCtBlocks.mkS (mkS c pcB (upd R 30#5 pc) T ps0 m0 v)
        ((mkS c pcB (upd R 30#5 pc) T ps0 m0 v).readReg64 (.gpr 0x1e#5))
        (mkS c pcB (upd R 30#5 pc) T ps0 m0 v).sp m ps q =
      mkS c pc (Poly1305DebianCtBlocks.mkRegs ⟨upd R 30#5 pc⟩ q).regs T ps m v := by
  have e : (mkS c pcB (upd R 30#5 pc) T ps0 m0 v).readReg64 (.gpr 0x1e#5) = pc := by
    simp [upd_apply]
  rw [e]; rfl

set_option maxHeartbeats 1000000 in
/-- `bl poly1305_blocks` at `pc` in both runs, with `x0`, `x1`, `x2` equal, the accumulator `rh`
at `x0`, the `final` byte at `x0 + 88` and the message (`x2` bytes, a nonzero multiple of 16) at
`x1`. Both runs come back at `pc + 4` with `x1..x17` and the flags anything, the other registers
as at the call (and `x30 = pc + 4`), new accumulator bytes, the rest of memory unchanged. -/
theorem call2 {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}
    (hc : StopCompat stop₁ stop₂) (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {c₁ c₂ : State} (hr₁ : c₁.status = .Running) (hr₂ : c₂.status = .Running)
    {pc T off : BitVec 64} {R₁ R₂ : BitVec 5 → BitVec 64} {ps₁ ps₂ : PState} {m₁ m₂ : Memory}
    (hcl₁ : (P pl X).CodeLoaded m₁) (hcl₂ : (P pl X).CodeLoaded m₂)
    (hf1 : (P pl X).fetchMem m₁ pc = some (.bl off)) (hf2 : (P pl X).fetchMem m₂ pc = some (.bl off))
    (hoff : pc + off = pl.base + 416#64)
    (hx0 : R₁ 0#5 = R₂ 0#5) (hx1 : R₁ 1#5 = R₂ 1#5) (hx2 : R₁ 2#5 = R₂ 2#5)
    {F₁ F₂ : SepProp} {ro₁ ro₂ : Bool} {rh₁ rh₂ : List (BitVec 8)} {fin₁ fin₂ : BitVec 8}
    {msg₁ msg₂ : List (BitVec 8)}
    (hl₁ : rh₁.length = 48) (hl₂ : rh₂.length = 48)
    (hn₁ : (R₁ 2#5).toNat = msg₁.length) (hn₂ : (R₂ 2#5).toNat = msg₂.length)
    (h16 : 16 ≤ msg₁.length) (h16d : msg₁.length % 16 = 0)
    (hm₁ : m₁ ⊨ (R₁ 0#5 ↦ₛ rh₁) ∗ ((R₁ 0#5 + 88#64) ↦ₛ [fin₁]) ∗ bytesIn ro₁ (R₁ 1#5) msg₁ ∗ F₁)
    (hm₂ : m₂ ⊨ (R₂ 0#5 ↦ₛ rh₂) ∗ ((R₂ 0#5 + 88#64) ↦ₛ [fin₂]) ∗ bytesIn ro₂ (R₂ 1#5) msg₂ ∗ F₂)
    (K : ∀ (m₁' m₂' : Memory) (ps₁' ps₂' : PState) (q₁ q₂ : Nat → BitVec 64)
      (rh₁' rh₂' : List (BitVec 8)),
      (P pl X).CodeLoaded m₁' → (P pl X).CodeLoaded m₂' → rh₁'.length = 48 → rh₂'.length = 48 →
      (m₁' ⊨ (R₁ 0#5 ↦ₛ rh₁') ∗ ((R₁ 0#5 + 88#64) ↦ₛ [fin₁]) ∗ bytesIn ro₁ (R₁ 1#5) msg₁ ∗ F₁) →
      (m₂' ⊨ (R₂ 0#5 ↦ₛ rh₂') ∗ ((R₂ 0#5 + 88#64) ↦ₛ [fin₂]) ∗ bytesIn ro₂ (R₂ 1#5) msg₂ ∗ F₂) →
      ObsEquiv (P pl X) arity stop₁ stop₂
        (mkS c₁ (pc + 4#64) (Poly1305DebianCtBlocks.mkRegs ⟨upd R₁ 30#5 (pc + 4#64)⟩ q₁).regs T
          ps₁' m₁' c₁.vregs.regs)
        (mkS c₂ (pc + 4#64) (Poly1305DebianCtBlocks.mkRegs ⟨upd R₂ 30#5 (pc + 4#64)⟩ q₂).regs T
          ps₂' m₂' c₂.vregs.regs)) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pc R₁ T ps₁ m₁ c₁.vregs.regs)
      (mkS c₂ pc R₂ T ps₂ m₂ c₂.vregs.regs) := by
  refine rs hc hr₁ hr₂ hf1 hf2 (ex_bl _) (ex_bl _) rfl ?_
  rw [hoff]
  have u0 : ∀ R : BitVec 5 → BitVec 64, upd R 30#5 (pc + 4#64) 0#5 = R 0#5 := fun R => by
    simp [upd_apply]
  have u1 : ∀ R : BitVec 5 → BitVec 64, upd R 30#5 (pc + 4#64) 1#5 = R 1#5 := fun R => by
    simp [upd_apply]
  have u2 : ∀ R : BitVec 5 → BitVec 64, upd R 30#5 (pc + 4#64) 2#5 = R 2#5 := fun R => by
    simp [upd_apply]
  refine blocks_rel_sep' (F₁ := F₁) (F₂ := F₂) hc hP hr₁ hr₂ rfl rfl hcl₁ hcl₂ rfl
    (by simp [Poly1305DebianCtBlocks.X0, u0, hx0]) (by simp [u1, hx1]) (by simp [u2, hx2])
    (by rw [blocksPre_mkS, u0, u1, u2, sat_pure_sep]; exact ⟨⟨hl₁, hn₁, h16, h16d⟩, hm₁⟩)
    (by rw [blocksPre_mkS, u0, u1, u2, sat_pure_sep]
        exact ⟨⟨hl₂, hn₂, by rw [← hn₂, ← hx2, hn₁]; exact h16,
          by rw [← hn₂, ← hx2, hn₁]; exact h16d⟩, hm₂⟩) ?_
  intro m₁' m₂' ps₁' ps₂' q₁ q₂ rh₁' rh₂' k₁ k₂ h₁ h₂
  rw [ret_eq, ret_eq]
  rw [blocksPre_mkS, u0, u1, u2, sat_pure_sep] at h₁ h₂
  exact K m₁' m₂' ps₁' ps₂' q₁ q₂ rh₁' rh₂' k₁ k₂ h₁.1.1 h₂.1.1 h₁.2 h₂.2

end Poly1305DebianCtUpdate

end
end

section
section
/-! # GCC's byte-copy loop in both runs

`L: ldrb wT, [xS, xI]; strb wT, [xD, xI]; add xI, xI, #1; cmp xC, xI; b.ne L` copies the bytes
`xI .. xC - 1` of the source at `xS` to the destination at `xD`. Both runs read the source at
`xS + i` and write the destination at `xD + i` for the same `i`, and leave the loop together;
the byte copied (in `xT`) differs. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtUpdate

open Arm64 Arm64.Obj Poly1305DebianCt Leakage Poly1305DebianCtFw
open Poly1305Libsodium (u64At bytesIn)

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_ldrb' (t n k : BitVec 5) (ht : t ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (a : BitVec 64) (ha : r n + r k = a) (hr : m.canRead a 1 = true) :
    execInstWithSvc svc (.ldr .W32 .B8 false (.gpr t) (.RegOffset (.gpr n) (.gpr k) .UXTX 0))
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r t ((m.read8 a).zeroExtend 64)) sp ps m v := by
  subst ha; exact ex_ldrb_reg t n k ht hn hk hr

theorem ex_strb' (t n k : BitVec 5) (ht : t ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (a : BitVec 64) (ha : r n + r k = a) (hw : m.canWrite a 1 = true) :
    execInstWithSvc svc (.str .B8 (.gpr t) (.RegOffset (.gpr n) (.gpr k) .UXTX 0))
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write8 a ((r t).truncate 8)) v := by
  subst ha; exact ex_strb_reg t n k ht hn hk hw

theorem ex_add_imm' (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (imm : BitVec 12)
    (z : BitVec 64) (hz : r n + imm.zeroExtend 64 = z) :
    execInstWithSvc svc (.addSubImm .W64 .ADD (.gpr d) (.gpr n) imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d z) sp ps m v := by
  rw [ex_add_imm d n hd hn imm, hz]

theorem ex_cmp_reg' (n k : BitVec 5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) (y z : BitVec 64)
    (hy : r n = y) (hz : r k = z) :
    execInstWithSvc svc (.addSubShift .W64 .SUBS .xzr (.gpr n) (.gpr k) .LSL 0)
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp (AddWithCarry64 y (~~~z) true).2 m v := by
  rw [ex_cmp_reg n k hn hk, hy, hz]

theorem ex_cmp_imm' (n : BitVec 5) (hn : n ≠ 31#5) (imm : BitVec 12) (y : BitVec 64)
    (hy : r n = y) :
    execInstWithSvc svc (.addSubImm .W64 .SUBS .xzr (.gpr n) imm false) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp (AddWithCarry64 y (~~~(imm.zeroExtend 64)) true).2 m v := by
  rw [ex_cmp_imm n hn imm, hy]

theorem ex_sub_shift0' (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (z : BitVec 64) (hz : r n - r k = z) :
    execInstWithSvc svc (.addSubShift .W64 .SUB (.gpr d) (.gpr n) (.gpr k) .LSL 0)
        (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) (upd r d z) sp ps m v := by
  rw [ex_sub_shift0 d n k hd hn hk, hz]

theorem ex_add_shift0' (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (z : BitVec 64) (hz : r n + r k = z) :
    execInstWithSvc svc (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSL 0)
        (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) (upd r d z) sp ps m v := by
  rw [ex_add_shift0 d n k hd hn hk, hz]

theorem ex_movz64' (d : BitVec 5) (hd : d ≠ 31#5) (imm : BitVec 16) (z : BitVec 64)
    (hz : imm.zeroExtend 64 = z) :
    execInstWithSvc svc (.moveWide .W64 .MOVZ (.gpr d) imm 0) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d z) sp ps m v := by
  rw [ex_movz64 d hd imm, hz]

theorem ex_mov' (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (x : BitVec 64) (hx : r n = x) :
    execInstWithSvc svc (.logicalShift .W64 .ORR (.gpr d) .xzr (.gpr n) .LSL 0)
        (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) (upd r d x) sp ps m v := by
  rw [ex_mov d n hd hn, hx]

theorem ex_csel' (c : CondCode) (d n k : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5)
    (hk : k ≠ 31#5) (z : BitVec 64) (hz : (if ConditionHolds c ps = true then r n else r k) = z) :
    execInstWithSvc svc (.condSelect .W64 .CSEL (.gpr d) (.gpr n) (.gpr k) c)
        (mkS s0 pc r sp ps m v) = mkS s0 (pc + 4#64) (upd r d z) sp ps m v := by
  rw [ex_csel c d n k hd hn hk, hz]

theorem ex_and_imm' (d n : BitVec 5) (hd : d ≠ 31#5) (hn : n ≠ 31#5) (mask : BitVec 64)
    (z : BitVec 64) (hz : r n &&& mask = z) :
    execInstWithSvc svc (.logicalImm .W64 .AND (.gpr d) (.gpr n) mask) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r d z) sp ps m v := by
  rw [ex_and_imm d n hd hn mask, hz]

theorem ex_ldr64_gpr' (a n : BitVec 5) (ha : a ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    (addr : BitVec 64) (he : r n + off = addr) (hr : m.canRead addr 8 = true) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr a) (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r a (m.read64 addr)) sp ps m v := by
  subst he; exact ex_ldr64_gpr a n ha hn off hr

theorem ex_str64_gpr' (a n : BitVec 5) (ha : a ≠ 31#5) (hn : n ≠ 31#5) (off : BitVec 64)
    (addr val : BitVec 64) (he : r n + off = addr) (hv : r a = val)
    (hw : m.canWrite addr 8 = true) :
    execInstWithSvc svc (.str .X64 (.gpr a) (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write64 addr val) v := by
  subst he hv; exact ex_str64_gpr a n ha hn off hw

theorem ex_str64_xzr' (n : BitVec 5) (hn : n ≠ 31#5) (off : BitVec 64)
    (addr : BitVec 64) (he : r n + off = addr) (hw : m.canWrite addr 8 = true) :
    execInstWithSvc svc (.str .X64 .xzr (.Offset (.gpr n) off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write64 addr 0#64) v := by
  subst he; exact ex_str64_xzr n hn off hw

end exec

section loop

variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

set_option maxHeartbeats 4000000 in
theorem copyLoop2 (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State}
    (hr₁ : c₁.status = .Running) (hr₂ : c₂.status = .Running) (pc sp : BitVec 64)
    (s t d c x : BitVec 5)
    (hs : s ≠ 31#5) (ht : t ≠ 31#5) (hd : d ≠ 31#5) (hcc : c ≠ 31#5) (hx : x ≠ 31#5)
    (hts : t ≠ s) (htd : t ≠ d) (htc : t ≠ c) (htx : t ≠ x)
    (hxs : x ≠ s) (hxd : x ≠ d) (hxc : x ≠ c)
    (hf1 : ∀ m', (P pl X).CodeLoaded m' → (P pl X).fetchMem m' pc =
      some (.ldr .W32 .B8 false (.gpr t) (.RegOffset (.gpr s) (.gpr x) .UXTX 0)))
    (hf2 : ∀ m', (P pl X).CodeLoaded m' → (P pl X).fetchMem m' (pc + 4#64) =
      some (.str .B8 (.gpr t) (.RegOffset (.gpr d) (.gpr x) .UXTX 0)))
    (hf3 : ∀ m', (P pl X).CodeLoaded m' → (P pl X).fetchMem m' (pc + 8#64) =
      some (.addSubImm .W64 .ADD (.gpr x) (.gpr x) 0x001#12 false))
    (hf4 : ∀ m', (P pl X).CodeLoaded m' → (P pl X).fetchMem m' (pc + 12#64) =
      some (.addSubShift .W64 .SUBS .xzr (.gpr c) (.gpr x) .LSL 0))
    (hf5 : ∀ m', (P pl X).CodeLoaded m' → (P pl X).fetchMem m' (pc + 16#64) =
      some (.bCond .NE 0xfffffffffffffff0#64))
    (Pa A : BitVec 64) (i0 j0 cnt : Nat) (hcnt : cnt < 2 ^ 64)
    (ro₁ ro₂ : Bool) (S₁ S₂ : List (BitVec 8)) (F₁ F₂ : SepProp)
    (hS₁ : i0 + cnt ≤ S₁.length) (hS₂ : i0 + cnt ≤ S₂.length) :
    ∀ k : Nat, 0 < k →
    ∀ (i : Nat) (r₁ r₂ : BitVec 5 → BitVec 64) (ps₁ ps₂ : PState) (m₁ m₂ : Memory)
      (D₁ D₂ : List (BitVec 8)),
    i + k = cnt → j0 + cnt ≤ D₁.length → j0 + cnt ≤ D₂.length →
    (P pl X).CodeLoaded m₁ → (P pl X).CodeLoaded m₂ →
    r₁ s = Pa + BitVec.ofNat 64 i0 → r₂ s = Pa + BitVec.ofNat 64 i0 →
    r₁ d = A + BitVec.ofNat 64 j0 → r₂ d = A + BitVec.ofNat 64 j0 →
    r₁ c = BitVec.ofNat 64 cnt → r₂ c = BitVec.ofNat 64 cnt →
    r₁ x = BitVec.ofNat 64 i → r₂ x = BitVec.ofNat 64 i →
    (m₁ ⊨ bytesIn ro₁ Pa S₁ ∗ (A ↦ₛ D₁) ∗ F₁) → (m₂ ⊨ bytesIn ro₂ Pa S₂ ∗ (A ↦ₛ D₂) ∗ F₂) →
    (∀ (r₁' r₂' : BitVec 5 → BitVec 64) (ps₁' ps₂' : PState) (m₁' m₂' : Memory)
        (D₁' D₂' : List (BitVec 8)),
      (P pl X).CodeLoaded m₁' → (P pl X).CodeLoaded m₂' →
      (∀ y, y ≠ t → y ≠ x → r₁' y = r₁ y) → (∀ y, y ≠ t → y ≠ x → r₂' y = r₂ y) →
      r₁' x = BitVec.ofNat 64 cnt → r₂' x = BitVec.ofNat 64 cnt →
      D₁'.length = D₁.length → D₂'.length = D₂.length →
      (m₁' ⊨ bytesIn ro₁ Pa S₁ ∗ (A ↦ₛ D₁') ∗ F₁) → (m₂' ⊨ bytesIn ro₂ Pa S₂ ∗ (A ↦ₛ D₂') ∗ F₂) →
      ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ (pc + 20#64) r₁' sp ps₁' m₁' c₁.vregs.regs)
        (mkS c₂ (pc + 20#64) r₂' sp ps₂' m₂' c₂.vregs.regs)) →
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pc r₁ sp ps₁ m₁ c₁.vregs.regs)
      (mkS c₂ pc r₂ sp ps₂ m₂ c₂.vregs.regs) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
  intro _ i r₁ r₂ ps₁ ps₂ m₁ m₂ D₁ D₂ hik hD₁ hD₂ hcl₁ hcl₂ hs₁ hs₂ hd₁ hd₂ hc₁ hc₂ hx₁ hx₂ hm₁
    hm₂ K
  have hi₁ : i0 + i < S₁.length := by omega
  have hi₂ : i0 + i < S₂.length := by omega
  have hj₁ : j0 + i < D₁.length := by omega
  have hj₂ : j0 + i < D₂.length := by omega
  have hcr₁ := src_byte hm₁ (i0 + i) hi₁
  have hcr₂ := src_byte hm₂ (i0 + i) hi₂
  have hm₁' : m₁ ⊨ (A ↦ₛ D₁) ∗ (bytesIn ro₁ Pa S₁ ∗ F₁) := Satisfies.of_eq hm₁
  have hm₂' : m₂ ⊨ (A ↦ₛ D₂) ∗ (bytesIn ro₂ Pa S₂ ∗ F₂) := Satisfies.of_eq hm₂
  have hcw₁ := dst_byte hm₁' (j0 + i) hj₁
  have hcw₂ := dst_byte hm₂' (j0 + i) hj₂
  have eS₁ : r₁ s + r₁ x = Pa + BitVec.ofNat 64 (i0 + i) := by rw [hs₁, hx₁, pc_add]
  have eS₂ : r₂ s + r₂ x = Pa + BitVec.ofNat 64 (i0 + i) := by rw [hs₂, hx₂, pc_add]
  -- ldrb
  refine rs hc hr₁ hr₂ (hf1 m₁ hcl₁) (hf1 m₂ hcl₂) (ex_ldrb' t s x ht hs hx _ eS₁ hcr₁)
    (ex_ldrb' t s x ht hs hx _ eS₂ hcr₂)
    (by simp [leakedValues, evalAddrMode, extendVal, hs, hx, hs₁, hs₂, hx₁, hx₂]) ?_
  generalize (m₁.read8 (Pa + BitVec.ofNat 64 (i0 + i))).zeroExtend 64 = b₁
  generalize (m₂.read8 (Pa + BitVec.ofNat 64 (i0 + i))).zeroExtend 64 = b₂
  have eD₁ : upd r₁ t b₁ d + upd r₁ t b₁ x = A + BitVec.ofNat 64 (j0 + i) := by
    rw [upd_ne _ _ (Ne.symm htd), upd_ne _ _ (Ne.symm htx), hd₁, hx₁, pc_add]
  have eD₂ : upd r₂ t b₂ d + upd r₂ t b₂ x = A + BitVec.ofNat 64 (j0 + i) := by
    rw [upd_ne _ _ (Ne.symm htd), upd_ne _ _ (Ne.symm htx), hd₂, hx₂, pc_add]
  -- strb
  refine rsw hc hr₁ hr₂ hcl₁ hcl₂ (hf2 m₁ hcl₁) (hf2 m₂ hcl₂) (ex_strb' t d x ht hd hx _ eD₁ hcw₁)
    (ex_strb' t d x ht hd hx _ eD₂ hcw₂)
    (by simp only [leakedValues, evalAddrMode, mkS_readGpr, if_neg hd, if_neg hx]
        simp [extendVal, Ne.symm htd, Ne.symm htx, hd₁, hd₂, hx₁, hx₂])
    ?_
  intro hcl₁' hcl₂'
  have hW₁ := sat_bytes_write hm₁' (j0 + i) hj₁ ((upd r₁ t b₁ t).truncate 8)
  have hW₂ := sat_bytes_write hm₂' (j0 + i) hj₂ ((upd r₂ t b₂ t).truncate 8)
  generalize m₁.write8 (A + BitVec.ofNat 64 (j0 + i)) ((upd r₁ t b₁ t).truncate 8) = n₁
    at hW₁ hcl₁' ⊢
  generalize m₂.write8 (A + BitVec.ofNat 64 (j0 + i)) ((upd r₂ t b₂ t).truncate 8) = n₂
    at hW₂ hcl₂' ⊢
  simp only [mkS_mem] at hcl₁' hcl₂'
  rw [show pc + 4#64 + 4#64 = pc + 8#64 by bv_omega]
  -- add x, x, #1
  have ex₁ : upd r₁ t b₁ x + (0x001#12 : BitVec 12).zeroExtend 64 = BitVec.ofNat 64 (i + 1) := by
    rw [upd_ne _ _ (Ne.symm htx), hx₁, show (0x001#12 : BitVec 12).zeroExtend 64 = 1#64 from rfl,
      ofNat_succ]
  have ex₂ : upd r₂ t b₂ x + (0x001#12 : BitVec 12).zeroExtend 64 = BitVec.ofNat 64 (i + 1) := by
    rw [upd_ne _ _ (Ne.symm htx), hx₂, show (0x001#12 : BitVec 12).zeroExtend 64 = 1#64 from rfl,
      ofNat_succ]
  refine rs hc hr₁ hr₂ (hf3 n₁ hcl₁') (hf3 n₂ hcl₂') (ex_add_imm' x x hx hx _ _ ex₁)
    (ex_add_imm' x x hx hx _ _ ex₂) rfl ?_
  rw [show pc + 8#64 + 4#64 = pc + 12#64 by bv_omega]
  -- cmp c, x
  have ec₁ : upd (upd r₁ t b₁) x (BitVec.ofNat 64 (i + 1)) c = BitVec.ofNat 64 cnt := by
    rw [upd_ne _ _ hxc.symm, upd_ne _ _ (Ne.symm htc), hc₁]
  have ec₂ : upd (upd r₂ t b₂) x (BitVec.ofNat 64 (i + 1)) c = BitVec.ofNat 64 cnt := by
    rw [upd_ne _ _ hxc.symm, upd_ne _ _ (Ne.symm htc), hc₂]
  refine rs hc hr₁ hr₂ (hf4 n₁ hcl₁') (hf4 n₂ hcl₂') (ex_cmp_reg' c x hcc hx _ _ ec₁ (upd_same _ _ _))
    (ex_cmp_reg' c x hcc hx _ _ ec₂ (upd_same _ _ _)) rfl ?_
  rw [show pc + 12#64 + 4#64 = pc + 16#64 by bv_omega]
  -- b.ne
  refine rs hc hr₁ hr₂ (hf5 n₁ hcl₁') (hf5 n₂ hcl₂') (ex_bcond _ _) (ex_bcond _ _) rfl ?_
  rw [ne_cmp, show decide (BitVec.ofNat 64 cnt ≠ BitVec.ofNat 64 (i + 1)) =
    decide (cnt ≠ i + 1) from by
      simp only [decide_eq_decide]; exact ne_ofNat_iff cnt (i + 1) hcnt (by omega)]
  by_cases hk0 : k = 0
  · subst hk0
    have e1 : ¬ (cnt ≠ i + 1) := by omega
    simp only [e1, decide_false, Bool.false_eq_true, if_false]
    rw [show pc + 16#64 + 4#64 = pc + 20#64 by bv_omega]
    refine K _ _ _ _ _ _ _ _ hcl₁' hcl₂' ?_ ?_ ?_ ?_ (List.length_set ..) (List.length_set ..)
      (Satisfies.of_eq hW₁) (Satisfies.of_eq hW₂)
    · intro y h1 h2; simp [upd_apply, h1, h2]
    · intro y h1 h2; simp [upd_apply, h1, h2]
    · simp only [upd_same]; congr 1 <;> omega
    · simp only [upd_same]; congr 1 <;> omega
  · have e1 : cnt ≠ i + 1 := by omega
    simp only [e1, ne_eq, not_false_eq_true, decide_true, if_true]
    rw [show pc + 16#64 + 0xfffffffffffffff0#64 = pc by bv_omega]
    refine ih (by omega) (i + 1) _ _ _ _ n₁ n₂ (D₁.set (j0 + i) ((upd r₁ t b₁ t).truncate 8))
      (D₂.set (j0 + i) ((upd r₂ t b₂ t).truncate 8)) (by omega) (by simp; omega) (by simp; omega)
      hcl₁' hcl₂' ?_ ?_ ?_ ?_ ?_ ?_ (upd_same _ _ _) (upd_same _ _ _)
      (Satisfies.of_eq hW₁) (Satisfies.of_eq hW₂) ?_
    · simp [upd_apply, Ne.symm hxs, Ne.symm hts, hs₁]
    · simp [upd_apply, Ne.symm hxs, Ne.symm hts, hs₂]
    · simp [upd_apply, Ne.symm hxd, Ne.symm htd, hd₁]
    · simp [upd_apply, Ne.symm hxd, Ne.symm htd, hd₂]
    · simp [upd_apply, Ne.symm hxc, Ne.symm htc, hc₁]
    · simp [upd_apply, Ne.symm hxc, Ne.symm htc, hc₂]
    · intro r₁' r₂' ps₁' ps₂' m₁' m₂' D₁' D₂' k₁ k₂ o₁ o₂ x₁ x₂ l₁ l₂ h₁ h₂
      refine K r₁' r₂' ps₁' ps₂' m₁' m₂' D₁' D₂' k₁ k₂ ?_ ?_ x₁ x₂ (l₁.trans (List.length_set ..))
        (l₂.trans (List.length_set ..)) h₁ h₂
      · intro y h1 h2; rw [o₁ y h1 h2]; simp [upd_apply, h1, h2]
      · intro y h1 h2; rw [o₂ y h1 h2]; simp [upd_apply, h1, h2]

end loop

end Poly1305DebianCtUpdate

end
end

section
section
/-! # `poly1305_update`, text offsets 840–888 in both runs: "store leftover"

With `leftover = 0`, `x18` at the message's byte `j` and `x4 = c` (`0 < c < 16`) bytes left, both
runs copy them into the buffer (the same addresses `m + j + i`, `st + 72 + i`), store `leftover = c`
and go to the epilogue at 892 (the exit continuation `ExitK2`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtUpdate

open Arm64 Arm64.Obj Poly1305DebianCt Leakage Poly1305DebianCtFw
open Poly1305Libsodium (u64At bytesIn)

theorem pcN (b : BitVec 64) (x k y : Nat) (h : x + k = y := by decide) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 k = b + BitVec.ofNat 64 y := by
  rw [pc_add, h]

theorem Kept.frame {r r' r0 : BitVec 5 → BitVec 64} {t x : BitVec 5} (hk : Kept r r0)
    (o : ∀ y, y ≠ t → y ≠ x → r' y = r y) (ht : t.toNat < 19) (hx : x.toNat < 19) :
    Kept r' r0 := by
  intro k h1 h2 h3
  rw [o k (by rintro rfl; omega) (by rintro rfl; omega)]
  exact hk k h1 h2 h3

/-- The exit continuation at the epilogue `pcE`: both runs with the stack pointer at the frame `T`,
the registers `x19..x28` of their entries, and memory `Mem` with the same `leftover` `lo`, whose
value is `tgt`. -/
def ExitK2 (pl : Placement) (X : String → Option (State → State)) (stop₁ stop₂ : State → Prop)
    (c₁ c₂ : State) (d₁ d₂ : RunD) (pcE a p T : BitVec 64) (tgt : Nat) : Prop :=
  ∀ (r₁ r₂ : BitVec 5 → BitVec 64) (ps₁ ps₂ : PState) (m₁ m₂ : Memory)
    (rh₁ rh₂ buf₁ buf₂ : List (BitVec 8)) (lo u2₁ u3₁ u2₂ u3₂ : BitVec 64),
    (P pl X).CodeLoaded m₁ → (P pl X).CodeLoaded m₂ → Kept r₁ c₁.regs.regs →
    Kept r₂ c₂.regs.regs → rh₁.length = 48 → rh₂.length = 48 → buf₁.length = 16 →
    buf₂.length = 16 → lo.toNat = tgt →
    (m₁ ⊨ Mem c₁ d₁ a p T lo rh₁ buf₁ u2₁ u3₁) → (m₂ ⊨ Mem c₂ d₂ a p T lo rh₂ buf₂ u2₂ u3₂) →
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ pcE r₁ T ps₁ m₁ c₁.vregs.regs)
      (mkS c₂ pcE r₂ T ps₂ m₂ c₂.vregs.regs)

section seg

variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

set_option maxHeartbeats 4000000 in
theorem seg840 (hc : StopCompat stop₁ stop₂) (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {c₁ c₂ : State} (hr₁ : c₁.status = .Running) (hr₂ : c₂.status = .Running)
    {d₁ d₂ : RunD} {a p T : BitVec 64} {tgt : Nat}
    (K : ExitK2 pl X stop₁ stop₂ c₁ c₂ d₁ d₂ (pl.base + 892#64) a p T tgt)
    {r₁ r₂ : BitVec 5 → BitVec 64} {ps₁ ps₂ : PState} {m₁ m₂ : Memory}
    (hcl₁ : (P pl X).CodeLoaded m₁) (hcl₂ : (P pl X).CodeLoaded m₂)
    (hk₁ : Kept r₁ c₁.regs.regs) (hk₂ : Kept r₂ c₂.regs.regs)
    (j cc : Nat) (hc0 : 0 < cc) (hc16 : cc < 16) (htgt : tgt = cc)
    (hlen₁ : d₁.msg.length = j + cc) (hlen₂ : d₂.msg.length = j + cc)
    (h0₁ : r₁ 0#5 = a) (h0₂ : r₂ 0#5 = a)
    (h18₁ : r₁ 18#5 = p + BitVec.ofNat 64 j) (h18₂ : r₂ 18#5 = p + BitVec.ofNat 64 j)
    (h4₁ : r₁ 4#5 = BitVec.ofNat 64 cc) (h4₂ : r₂ 4#5 = BitVec.ofNat 64 cc)
    {rh₁ rh₂ buf₁ buf₂ : List (BitVec 8)} (hrh₁ : rh₁.length = 48) (hrh₂ : rh₂.length = 48)
    (hb₁ : buf₁.length = 16) (hb₂ : buf₂.length = 16) {u2₁ u3₁ u2₂ u3₂ : BitVec 64}
    (hm₁ : m₁ ⊨ Mem c₁ d₁ a p T 0#64 rh₁ buf₁ u2₁ u3₁)
    (hm₂ : m₂ ⊨ Mem c₂ d₂ a p T 0#64 rh₂ buf₂ u2₂ u3₂) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 840#64) r₁ T ps₁ m₁ c₁.vregs.regs)
      (mkS c₂ (pl.base + 840#64) r₂ T ps₂ m₂ c₂.vregs.regs) := by
  generalize hW₁ : (a ↦ₛ rh₁) ∗ ((a + 88#64) ↦ₛ [d₁.fin]) ∗ ((a + 48#64) ↦ₛ d₁.pad) ∗
    ((a + 89#64) ↦ₛ d₁.rest) ∗ Cells4 T (c₁.regs.regs 29#5) (c₁.regs.regs 30#5) u2₁ u3₁ ∗ d₁.R = W₁
  generalize hW₂ : (a ↦ₛ rh₂) ∗ ((a + 88#64) ↦ₛ [d₂.fin]) ∗ ((a + 48#64) ↦ₛ d₂.pad) ∗
    ((a + 89#64) ↦ₛ d₂.rest) ∗ Cells4 T (c₂.regs.regs 29#5) (c₂.regs.regs 30#5) u2₂ u3₂ ∗ d₂.R = W₂
  have hm1₁ : m₁ ⊨ ((a + 64#64) ↦₆₄ 0#64) ∗ (bytesIn d₁.ro p d₁.msg ∗ ((a + 72#64) ↦ₛ buf₁) ∗ W₁) :=
    Satisfies.of_eq hm₁ (by rw [← hW₁]; simp only [Mem, Fields]; ac_rfl)
  have hm1₂ : m₂ ⊨ ((a + 64#64) ↦₆₄ 0#64) ∗ (bytesIn d₂.ro p d₂.msg ∗ ((a + 72#64) ↦ₛ buf₂) ∗ W₂) :=
    Satisfies.of_eq hm₂ (by rw [← hW₂]; simp only [Mem, Fields]; ac_rfl)
  have c0₁ := sat64_read hm1₁
  have c0₂ := sat64_read hm1₂
  -- 840: ldr x5, [x0, #0x40]
  refine rs hc hr₁ hr₂ (f_98 hP hcl₁) (f_98 hP hcl₂)
    (ex_ldr64_gpr' 5#5 0#5 (by decide) (by decide) _ _ (by rw [h0₁]) c0₁.2.1)
    (ex_ldr64_gpr' 5#5 0#5 (by decide) (by decide) _ _ (by rw [h0₂]) c0₂.2.1)
    (by simp [leakedValues, evalAddrMode, h0₁, h0₂]) ?_
  rw [c0₁.1, c0₂.1, pc4 pl.base 840 844]
  -- 844: mov x3, #0
  refine rs hc hr₁ hr₂ (f_9c hP hcl₁) (f_9c hP hcl₂) (ex_movz64' 3#5 (by decide) _ 0#64 rfl)
    (ex_movz64' 3#5 (by decide) _ 0#64 rfl) rfl ?_
  rw [pc4 pl.base 844 848]
  -- 848: add x2, x5, #0x48
  refine rs hc hr₁ hr₂ (f_a0 hP hcl₁) (f_a0 hP hcl₂)
    (ex_add_imm' 2#5 5#5 (by decide) (by decide) _ 72#64 (by simp [upd_apply] <;> rfl))
    (ex_add_imm' 2#5 5#5 (by decide) (by decide) _ 72#64 (by simp [upd_apply] <;> rfl)) rfl ?_
  rw [pc4 pl.base 848 852]
  -- 852: add x2, x0, x2
  refine rs hc hr₁ hr₂ (f_a4 hP hcl₁) (f_a4 hP hcl₂)
    (ex_add_shift0' 2#5 0#5 2#5 (by decide) (by decide) (by decide) (a + 72#64)
      (by simp [upd_apply, h0₁]))
    (ex_add_shift0' 2#5 0#5 2#5 (by decide) (by decide) (by decide) (a + 72#64)
      (by simp [upd_apply, h0₂])) rfl ?_
  rw [pc4 pl.base 852 856]
  -- 856, 860: nop
  refine rs hc hr₁ hr₂ (f_a8 hP hcl₁) (f_a8 hP hcl₂) ex_nop ex_nop rfl ?_
  rw [pc4 pl.base 856 860]
  refine rs hc hr₁ hr₂ (f_ac hP hcl₁) (f_ac hP hcl₂) ex_nop ex_nop rfl ?_
  rw [pc4 pl.base 860 864]
  have hk1₁ := (((hk₁.upd 5#5 (by decide) 0#64).upd 3#5 (by decide) 0#64).upd 2#5 (by decide)
    72#64).upd 2#5 (by decide) (a + 72#64)
  have hk1₂ := (((hk₂.upd 5#5 (by decide) 0#64).upd 3#5 (by decide) 0#64).upd 2#5 (by decide)
    72#64).upd 2#5 (by decide) (a + 72#64)
  -- the loop at 864
  have hm2₁ : m₁ ⊨ bytesIn d₁.ro p d₁.msg ∗ ((a + 72#64) ↦ₛ buf₁) ∗ (((a + 64#64) ↦₆₄ 0#64) ∗ W₁) :=
    Satisfies.of_eq hm1₁
  have hm2₂ : m₂ ⊨ bytesIn d₂.ro p d₂.msg ∗ ((a + 72#64) ↦ₛ buf₂) ∗ (((a + 64#64) ↦₆₄ 0#64) ∗ W₂) :=
    Satisfies.of_eq hm1₂
  refine copyLoop2 hc hr₁ hr₂ (pl.base + 864#64) T 18#5 1#5 2#5 4#5 3#5
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun m' h => f_b0 hP h) (fun m' h => by rw [pc_add]; exact f_b4 hP h)
    (fun m' h => by rw [pc_add]; exact f_b8 hP h) (fun m' h => by rw [pc_add]; exact f_bc hP h)
    (fun m' h => by rw [pc_add]; exact f_c0 hP h)
    p (a + 72#64) j 0 cc (by omega) d₁.ro d₂.ro d₁.msg d₂.msg _ _ (by omega) (by omega)
    cc hc0 0 _ _ _ _ m₁ m₂ buf₁ buf₂ (by omega) (by omega) (by omega) hcl₁ hcl₂
    (by simp [upd_apply, h18₁]) (by simp [upd_apply, h18₂]) (by simp [upd_apply])
    (by simp [upd_apply]) (by simp [upd_apply, h4₁]) (by simp [upd_apply, h4₂])
    (by simp [upd_apply]) (by simp [upd_apply]) hm2₁ hm2₂ ?_
  intro r₁' r₂' ps₁' ps₂' m₁' m₂' D₁' D₂' k₁ k₂ o₁ o₂ x₁ x₂ l₁ l₂ h₁ h₂
  rw [pcN pl.base 864 20 884]
  have q0₁ : r₁' 0#5 = a := by rw [o₁ 0#5 (by decide) (by decide)]; simp [upd_apply, h0₁]
  have q0₂ : r₂' 0#5 = a := by rw [o₂ 0#5 (by decide) (by decide)]; simp [upd_apply, h0₂]
  have kk₁ := hk1₁.frame o₁ (by decide) (by decide)
  have kk₂ := hk1₂.frame o₂ (by decide) (by decide)
  -- 884: add x5, x5, x4
  refine rs hc hr₁ hr₂ (f_c4 hP k₁) (f_c4 hP k₂)
    (ex_add_shift0' 5#5 5#5 4#5 (by decide) (by decide) (by decide) (BitVec.ofNat 64 cc)
      (by rw [o₁ 5#5 (by decide) (by decide), o₁ 4#5 (by decide) (by decide)]
          simp [upd_apply, h4₁]))
    (ex_add_shift0' 5#5 5#5 4#5 (by decide) (by decide) (by decide) (BitVec.ofNat 64 cc)
      (by rw [o₂ 5#5 (by decide) (by decide), o₂ 4#5 (by decide) (by decide)]
          simp [upd_apply, h4₂])) rfl ?_
  rw [pc4 pl.base 884 888]
  -- 888: str x5, [x0, #0x40]
  have h3₁ : m₁' ⊨ ((a + 64#64) ↦₆₄ 0#64) ∗ (bytesIn d₁.ro p d₁.msg ∗ ((a + 72#64) ↦ₛ D₁') ∗ W₁) :=
    Satisfies.of_eq h₁
  have h3₂ : m₂' ⊨ ((a + 64#64) ↦₆₄ 0#64) ∗ (bytesIn d₂.ro p d₂.msg ∗ ((a + 72#64) ↦ₛ D₂') ∗ W₂) :=
    Satisfies.of_eq h₂
  have c1₁ := sat64_read h3₁
  have c1₂ := sat64_read h3₂
  refine rsw hc hr₁ hr₂ k₁ k₂ (f_c8 hP k₁) (f_c8 hP k₂)
    (ex_str64_gpr' 5#5 0#5 (by decide) (by decide) _ _ (BitVec.ofNat 64 cc)
      (by rw [upd_ne _ _ (by decide), q0₁]) (upd_same _ _ _) c1₁.2.2)
    (ex_str64_gpr' 5#5 0#5 (by decide) (by decide) _ _ (BitVec.ofNat 64 cc)
      (by rw [upd_ne _ _ (by decide), q0₂]) (upd_same _ _ _) c1₂.2.2)
    (by simp [leakedValues, evalAddrMode, q0₁, q0₂]) ?_
  intro k₁' k₂'
  rw [pc4 pl.base 888 892]
  have w₁ := sat64_write h3₁ (BitVec.ofNat 64 cc)
  have w₂ := sat64_write h3₂ (BitVec.ofNat 64 cc)
  refine K _ _ _ _ _ _ rh₁ rh₂ D₁' D₂' (BitVec.ofNat 64 cc) u2₁ u3₁ u2₂ u3₂ k₁' k₂'
    (kk₁.upd 5#5 (by decide) _) (kk₂.upd 5#5 (by decide) _) hrh₁ hrh₂ (l₁.trans hb₁)
    (l₂.trans hb₂) (by rw [htgt]; simp; omega)
    (Satisfies.of_eq w₁ (by rw [← hW₁]; simp only [Mem, Fields]; ac_rfl))
    (Satisfies.of_eq w₂ (by rw [← hW₂]; simp only [Mem, Fields]; ac_rfl))

end seg

end Poly1305DebianCtUpdate

end
end

section
section
/-! # `poly1305_update`, text offsets 828–936 in both runs: "process full blocks"

With `leftover = 0`, `x18` at the message's byte `j` and `x4 = c` bytes left (the same in both
runs): when `c > 15` both runs call `poly1305_blocks` on the next `16 ⌊c/16⌋` message bytes
(`call2`); the rest (fewer than 16 bytes) goes to the buffer (`seg840`) or, when none is left, to
the epilogue at 784. Every branch depends on `c` only. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtUpdate

open Arm64 Arm64.Obj Poly1305DebianCt Leakage Poly1305DebianCtFw
open Poly1305Libsodium (u64At bytesIn)

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_stp64_sp' (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hw1 : m.canWrite (sp + off) 8 = true)
    (hw2 : m.canWrite (sp + off + 8#64) 8 = true) (va vb : BitVec 64) (hva : r a = va)
    (hvb : r b = vb) :
    execInstWithSvc svc (.stp .W64 (.gpr a) (.gpr b) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps ((m.write64 (sp + off) va).write64 (sp + off + 8#64) vb) v := by
  rw [ex_stp64_sp a b ha hb off hal hw1 hw2, hva, hvb]

theorem ex_ldp64_sp' (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hr1 : m.canRead (sp + off) 8 = true)
    (hr2 : m.canRead (sp + off + 8#64) 8 = true) (va vb : BitVec 64)
    (hva : m.read64 (sp + off) = va) (hvb : m.read64 (sp + off + 8#64) = vb) :
    execInstWithSvc svc (.ldp .W64 false (.gpr a) (.gpr b) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd (upd r a va) b vb) sp ps m v := by
  rw [ex_ldp64_sp a b ha hb off hal hr1 hr2, hva, hvb]

end exec

section seg

variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

set_option maxHeartbeats 8000000 in
theorem seg828 (hc : StopCompat stop₁ stop₂) (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {c₁ c₂ : State} (hr₁ : c₁.status = .Running) (hr₂ : c₂.status = .Running)
    {d₁ d₂ : RunD} {a p T : BitVec 64} {tgt : Nat}
    (K784 : ExitK2 pl X stop₁ stop₂ c₁ c₂ d₁ d₂ (pl.base + 784#64) a p T tgt)
    (K892 : ExitK2 pl X stop₁ stop₂ c₁ c₂ d₁ d₂ (pl.base + 892#64) a p T tgt)
    (hTal : T &&& 0b1111#64 = 0#64)
    {r₁ r₂ : BitVec 5 → BitVec 64} {ps₁ ps₂ : PState} {m₁ m₂ : Memory}
    (hcl₁ : (P pl X).CodeLoaded m₁) (hcl₂ : (P pl X).CodeLoaded m₂)
    (hk₁ : Kept r₁ c₁.regs.regs) (hk₂ : Kept r₂ c₂.regs.regs)
    (j cc : Nat) (htgt : tgt = cc % 16) (hml : j + cc < 2 ^ 64)
    (hlen₁ : d₁.msg.length = j + cc) (hlen₂ : d₂.msg.length = j + cc)
    (h0₁ : r₁ 0#5 = a) (h0₂ : r₂ 0#5 = a)
    (h18₁ : r₁ 18#5 = p + BitVec.ofNat 64 j) (h18₂ : r₂ 18#5 = p + BitVec.ofNat 64 j)
    (h4₁ : r₁ 4#5 = BitVec.ofNat 64 cc) (h4₂ : r₂ 4#5 = BitVec.ofNat 64 cc)
    {rh₁ rh₂ buf₁ buf₂ : List (BitVec 8)} (hrh₁ : rh₁.length = 48) (hrh₂ : rh₂.length = 48)
    (hb₁ : buf₁.length = 16) (hb₂ : buf₂.length = 16) {u2₁ u3₁ u2₂ u3₂ : BitVec 64}
    (hm₁ : m₁ ⊨ Mem c₁ d₁ a p T 0#64 rh₁ buf₁ u2₁ u3₁)
    (hm₂ : m₂ ⊨ Mem c₂ d₂ a p T 0#64 rh₂ buf₂ u2₂ u3₂) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 828#64) r₁ T ps₁ m₁ c₁.vregs.regs)
      (mkS c₂ (pl.base + 828#64) r₂ T ps₂ m₂ c₂.vregs.regs) := by
  have hc64 : cc < 2 ^ 64 := by omega
  -- 828: cmp x4, #15
  refine rs hc hr₁ hr₂ (f_8c hP hcl₁) (f_8c hP hcl₂) (ex_cmp_imm' 4#5 (by decide) _ _ h4₁)
    (ex_cmp_imm' 4#5 (by decide) _ _ h4₂) rfl ?_
  rw [pc4 pl.base 828 832]
  -- 832: b.hi 904
  refine rs hc hr₁ hr₂ (f_90 hP hcl₁) (f_90 hP hcl₂) (ex_bcond _ _) (ex_bcond _ _) rfl ?_
  rw [hi15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc64]
  by_cases hc15 : 15 < cc
  swap
  · -- c ≤ 15
    simp only [hc15, decide_false, Bool.false_eq_true, if_false]
    rw [pc4 pl.base 832 836]
    -- 836: cbz x4, 784
    refine rs hc hr₁ hr₂ (f_94 hP hcl₁) (f_94 hP hcl₂) (ex_cbz 4#5 (by decide) _)
      (ex_cbz 4#5 (by decide) _) rfl ?_
    rw [h4₁, h4₂]
    by_cases hc0 : cc = 0
    · have e0 : BitVec.ofNat 64 cc = 0#64 := by rw [hc0]
      rw [if_pos e0]
      rw [show pl.base + 836#64 + 0xffffffffffffffcc#64 = pl.base + 784#64 by bv_omega]
      exact K784 r₁ r₂ _ _ m₁ m₂ rh₁ rh₂ buf₁ buf₂ 0#64 u2₁ u3₁ u2₂ u3₂ hcl₁ hcl₂ hk₁ hk₂
        hrh₁ hrh₂ hb₁ hb₂ (by rw [htgt, hc0]; rfl) hm₁ hm₂
    · have e0 : BitVec.ofNat 64 cc ≠ 0#64 := fun e => hc0 ((ofNat_eq_zero cc hc64).mp e)
      rw [if_neg e0]
      rw [pc4 pl.base 836 840]
      exact seg840 hc hP hr₁ hr₂ K892 hcl₁ hcl₂ hk₁ hk₂ j cc (by omega) (by omega)
        (by rw [htgt]; omega) hlen₁ hlen₂ h0₁ h0₂ h18₁ h18₂ h4₁ h4₂ hrh₁ hrh₂ hb₁ hb₂ hm₁ hm₂
  · -- c > 15
    simp only [hc15, decide_true, if_true]
    rw [show pl.base + 832#64 + 0x0000000000000048#64 = pl.base + 904#64 by bv_omega]
    obtain ⟨B, hB⟩ : ∃ B, 16 * (cc / 16) = B := ⟨_, rfl⟩
    have hB16 : 16 ≤ B := by omega
    have hand : ∀ r : BitVec 5 → BitVec 64, r 4#5 = BitVec.ofNat 64 cc →
        r 4#5 &&& 0xfffffffffffffff0#64 = BitVec.ofNat 64 B := fun r h => by
      rw [h, and_mask_hi cc hc64, hB]
    -- 904: and x2, x4, #~15
    refine rs hc hr₁ hr₂ (f_d8 hP hcl₁) (f_d8 hP hcl₂)
      (ex_and_imm' 2#5 4#5 (by decide) (by decide) _ _ (hand r₁ h4₁))
      (ex_and_imm' 2#5 4#5 (by decide) (by decide) _ _ (hand r₂ h4₂)) rfl ?_
    rw [pc4 pl.base 904 908]
    -- 908: mov x1, x18
    refine rs hc hr₁ hr₂ (f_dc hP hcl₁) (f_dc hP hcl₂)
      (ex_mov' 1#5 18#5 (by decide) (by decide) (p + BitVec.ofNat 64 j) (by simp [upd_apply, h18₁]))
      (ex_mov' 1#5 18#5 (by decide) (by decide) (p + BitVec.ofNat 64 j) (by simp [upd_apply, h18₂]))
      rfl ?_
    rw [pc4 pl.base 908 912]
    have e0₁ : upd (upd r₁ 2#5 (BitVec.ofNat 64 B)) 1#5 (p + BitVec.ofNat 64 j) 0#5 = a := by
      simp [upd_apply, h0₁]
    have e0₂ : upd (upd r₂ 2#5 (BitVec.ofNat 64 B)) 1#5 (p + BitVec.ofNat 64 j) 0#5 = a := by
      simp [upd_apply, h0₂]
    have e1₁ : upd (upd r₁ 2#5 (BitVec.ofNat 64 B)) 1#5 (p + BitVec.ofNat 64 j) 1#5 =
        p + BitVec.ofNat 64 j := by simp [upd_apply]
    have e1₂ : upd (upd r₂ 2#5 (BitVec.ofNat 64 B)) 1#5 (p + BitVec.ofNat 64 j) 1#5 =
        p + BitVec.ofNat 64 j := by simp [upd_apply]
    have e2₁ : upd (upd r₁ 2#5 (BitVec.ofNat 64 B)) 1#5 (p + BitVec.ofNat 64 j) 2#5 =
        BitVec.ofNat 64 B := by simp [upd_apply]
    have e2₂ : upd (upd r₂ 2#5 (BitVec.ofNat 64 B)) 1#5 (p + BitVec.ofNat 64 j) 2#5 =
        BitVec.ofNat 64 B := by simp [upd_apply]
    have e4₁ : upd (upd r₁ 2#5 (BitVec.ofNat 64 B)) 1#5 (p + BitVec.ofNat 64 j) 4#5 =
        BitVec.ofNat 64 cc := by simp [upd_apply, h4₁]
    have e4₂ : upd (upd r₂ 2#5 (BitVec.ofNat 64 B)) 1#5 (p + BitVec.ofNat 64 j) 4#5 =
        BitVec.ofNat 64 cc := by simp [upd_apply, h4₂]
    have e18₁ : upd (upd r₁ 2#5 (BitVec.ofNat 64 B)) 1#5 (p + BitVec.ofNat 64 j) 18#5 =
        p + BitVec.ofNat 64 j := by simp [upd_apply, h18₁]
    have e18₂ : upd (upd r₂ 2#5 (BitVec.ofNat 64 B)) 1#5 (p + BitVec.ofNat 64 j) 18#5 =
        p + BitVec.ofNat 64 j := by simp [upd_apply, h18₂]
    have kR₁ := (hk₁.upd 2#5 (by decide) (BitVec.ofNat 64 B)).upd 1#5 (by decide)
      (p + BitVec.ofNat 64 j)
    have kR₂ := (hk₂.upd 2#5 (by decide) (BitVec.ofNat 64 B)).upd 1#5 (by decide)
      (p + BitVec.ofNat 64 j)
    generalize upd (upd r₁ 2#5 (BitVec.ofNat 64 B)) 1#5 (p + BitVec.ofNat 64 j) = R₁
      at e0₁ e1₁ e2₁ e4₁ e18₁ kR₁ ⊢
    generalize upd (upd r₂ 2#5 (BitVec.ofNat 64 B)) 1#5 (p + BitVec.ofNat 64 j) = R₂
      at e0₂ e1₂ e2₂ e4₂ e18₂ kR₂ ⊢
    -- 912: stp x2, x4, [sp, #16]
    generalize hW₁ : Fields a rh₁ d₁.pad 0#64 buf₁ d₁.fin d₁.rest ∗ bytesIn d₁.ro p d₁.msg ∗ d₁.R = W₁
    generalize hW₂ : Fields a rh₂ d₂.pad 0#64 buf₂ d₂.fin d₂.rest ∗ bytesIn d₂.ro p d₂.msg ∗ d₂.R = W₂
    have hm1₁ : m₁ ⊨ ((T + 0x10#64) ↦₆₄ u2₁) ∗ (((T + 0x10#64 + 8#64) ↦₆₄ u3₁) ∗
        (T ↦₆₄ c₁.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ c₁.regs.regs 30#5) ∗ W₁) :=
      Satisfies.of_eq hm₁ (by rw [← hW₁]; simp only [Mem, Cells4]; ac_rfl)
    have hm1₂ : m₂ ⊨ ((T + 0x10#64) ↦₆₄ u2₂) ∗ (((T + 0x10#64 + 8#64) ↦₆₄ u3₂) ∗
        (T ↦₆₄ c₂.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ c₂.regs.regs 30#5) ∗ W₂) :=
      Satisfies.of_eq hm₂ (by rw [← hW₂]; simp only [Mem, Cells4]; ac_rfl)
    have c2₁ := sat64_read hm1₁
    have c2₂ := sat64_read hm1₂
    have c3₁ := sat64_read (Satisfies.of_eq hm1₁ (Q := ((T + 0x10#64 + 8#64) ↦₆₄ u3₁) ∗
      (((T + 0x10#64) ↦₆₄ u2₁) ∗ (T ↦₆₄ c₁.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ c₁.regs.regs 30#5) ∗
        W₁)))
    have c3₂ := sat64_read (Satisfies.of_eq hm1₂ (Q := ((T + 0x10#64 + 8#64) ↦₆₄ u3₂) ∗
      (((T + 0x10#64) ↦₆₄ u2₂) ∗ (T ↦₆₄ c₂.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ c₂.regs.regs 30#5) ∗
        W₂)))
    refine rsw hc hr₁ hr₂ hcl₁ hcl₂ (f_e0 hP hcl₁) (f_e0 hP hcl₂)
      (ex_stp64_sp' 2#5 4#5 (by decide) (by decide) 0x10#64 hTal c2₁.2.2 c3₁.2.2 _ _ e2₁ e4₁)
      (ex_stp64_sp' 2#5 4#5 (by decide) (by decide) 0x10#64 hTal c2₂.2.2 c3₂.2.2 _ _ e2₂ e4₂)
      (by simp [leakedValues, evalAddrMode]) ?_
    intro hcl5₁ hcl5₂
    rw [pc4 pl.base 912 916]
    have w2₁ := sat64_write (Satisfies.of_eq (sat64_write hm1₁ (BitVec.ofNat 64 B))
      (Q := ((T + 0x10#64 + 8#64) ↦₆₄ u3₁) ∗ (((T + 0x10#64) ↦₆₄ BitVec.ofNat 64 B) ∗
        (T ↦₆₄ c₁.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ c₁.regs.regs 30#5) ∗ W₁)))
      (BitVec.ofNat 64 cc)
    have w2₂ := sat64_write (Satisfies.of_eq (sat64_write hm1₂ (BitVec.ofNat 64 B))
      (Q := ((T + 0x10#64 + 8#64) ↦₆₄ u3₂) ∗ (((T + 0x10#64) ↦₆₄ BitVec.ofNat 64 B) ∗
        (T ↦₆₄ c₂.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ c₂.regs.regs 30#5) ∗ W₂)))
      (BitVec.ofNat 64 cc)
    generalize (m₁.write64 (T + 0x10#64) (BitVec.ofNat 64 B)).write64 (T + 0x10#64 + 8#64)
      (BitVec.ofNat 64 cc) = n₁ at w2₁ hcl5₁ ⊢
    generalize (m₂.write64 (T + 0x10#64) (BitVec.ofNat 64 B)).write64 (T + 0x10#64 + 8#64)
      (BitVec.ofNat 64 cc) = n₂ at w2₂ hcl5₂ ⊢
    simp only [mkS_mem] at hcl5₁ hcl5₂
    rw [← hW₁, bytesIn_three d₁.ro p d₁.msg j B (by omega)] at w2₁
    rw [← hW₂, bytesIn_three d₂.ro p d₂.msg j B (by omega)] at w2₂
    simp only [Fields] at w2₁ w2₂
    -- 916: bl poly1305_blocks
    have hBl₁ : ((d₁.msg.drop j).take B).length = B := by simp; omega
    have hBl₂ : ((d₂.msg.drop j).take B).length = B := by simp; omega
    have hB64 : (BitVec.ofNat 64 B).toNat = B := by simp; omega
    refine call2 (F₁ := ((a + 72#64) ↦ₛ buf₁) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗ ((a + 48#64) ↦ₛ d₁.pad) ∗
          ((a + 89#64) ↦ₛ d₁.rest) ∗ bytesIn d₁.ro p (d₁.msg.take j) ∗
          bytesIn d₁.ro (p + BitVec.ofNat 64 j + BitVec.ofNat 64 B) ((d₁.msg.drop j).drop B) ∗
          Cells4 T (c₁.regs.regs 29#5) (c₁.regs.regs 30#5) (BitVec.ofNat 64 B) (BitVec.ofNat 64 cc) ∗
          d₁.R)
      (F₂ := ((a + 72#64) ↦ₛ buf₂) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗ ((a + 48#64) ↦ₛ d₂.pad) ∗
          ((a + 89#64) ↦ₛ d₂.rest) ∗ bytesIn d₂.ro p (d₂.msg.take j) ∗
          bytesIn d₂.ro (p + BitVec.ofNat 64 j + BitVec.ofNat 64 B) ((d₂.msg.drop j).drop B) ∗
          Cells4 T (c₂.regs.regs 29#5) (c₂.regs.regs 30#5) (BitVec.ofNat 64 B) (BitVec.ofNat 64 cc) ∗
          d₂.R) (ro₁ := d₁.ro) (ro₂ := d₂.ro) (fin₁ := d₁.fin) (fin₂ := d₂.fin)
      (msg₁ := (d₁.msg.drop j).take B) (msg₂ := (d₂.msg.drop j).take B) (rh₁ := rh₁) (rh₂ := rh₂)
      hc hP hr₁ hr₂ hcl5₁ hcl5₂ (f_e4 hP hcl5₁) (f_e4 hP hcl5₂) (by bv_omega)
      (e0₁.trans e0₂.symm) (e1₁.trans e1₂.symm) (e2₁.trans e2₂.symm) hrh₁ hrh₂
      (by rw [e2₁, hB64, hBl₁]) (by rw [e2₂, hB64, hBl₂]) (by omega) (by rw [hBl₁]; omega)
      (by rw [e0₁, e1₁]; exact Satisfies.of_eq w2₁ (by simp only [Cells4]; ac_rfl))
      (by rw [e0₂, e1₂]; exact Satisfies.of_eq w2₂ (by simp only [Cells4]; ac_rfl)) ?_
    intro n₁' n₂' ps₁' ps₂' q₁ q₂ rh₁' rh₂' k₁ k₂ l₁ l₂ h₁ h₂
    rw [e0₁, e1₁] at h₁
    rw [e0₂, e1₂] at h₂
    rw [pc4 pl.base 916 920]
    have f0₁ : (Poly1305DebianCtBlocks.mkRegs ⟨upd R₁ 30#5 (pl.base + 920#64)⟩ q₁).regs 0#5 = a := by
      rw [mkRegs_out _ _ _ (by decide), upd_ne _ _ (by decide), e0₁]
    have f0₂ : (Poly1305DebianCtBlocks.mkRegs ⟨upd R₂ 30#5 (pl.base + 920#64)⟩ q₂).regs 0#5 = a := by
      rw [mkRegs_out _ _ _ (by decide), upd_ne _ _ (by decide), e0₂]
    have f18₁ : (Poly1305DebianCtBlocks.mkRegs ⟨upd R₁ 30#5 (pl.base + 920#64)⟩ q₁).regs 18#5 =
        p + BitVec.ofNat 64 j := by
      rw [mkRegs_out _ _ _ (by decide), upd_ne _ _ (by decide), e18₁]
    have f18₂ : (Poly1305DebianCtBlocks.mkRegs ⟨upd R₂ 30#5 (pl.base + 920#64)⟩ q₂).regs 18#5 =
        p + BitVec.ofNat 64 j := by
      rw [mkRegs_out _ _ _ (by decide), upd_ne _ _ (by decide), e18₂]
    have kf₁ := (kR₁.upd 30#5 (by decide) (pl.base + 920#64)).mkRegs q₁
    have kf₂ := (kR₂.upd 30#5 (by decide) (pl.base + 920#64)).mkRegs q₂
    generalize (Poly1305DebianCtBlocks.mkRegs ⟨upd R₁ 30#5 (pl.base + 920#64)⟩ q₁).regs = Q₁
      at f0₁ f18₁ kf₁ ⊢
    generalize (Poly1305DebianCtBlocks.mkRegs ⟨upd R₂ 30#5 (pl.base + 920#64)⟩ q₂).regs = Q₂
      at f0₂ f18₂ kf₂ ⊢
    -- 920: ldp x2, x4, [sp, #16]
    generalize hV₁ : (a ↦ₛ rh₁') ∗ ((a + 88#64) ↦ₛ [d₁.fin]) ∗
      bytesIn d₁.ro (p + BitVec.ofNat 64 j) ((d₁.msg.drop j).take B) ∗
      ((a + 72#64) ↦ₛ buf₁) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗ ((a + 48#64) ↦ₛ d₁.pad) ∗
      ((a + 89#64) ↦ₛ d₁.rest) ∗ bytesIn d₁.ro p (d₁.msg.take j) ∗
      bytesIn d₁.ro (p + BitVec.ofNat 64 j + BitVec.ofNat 64 B) ((d₁.msg.drop j).drop B) ∗
      (T ↦₆₄ c₁.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ c₁.regs.regs 30#5) ∗ d₁.R = V₁
    generalize hV₂ : (a ↦ₛ rh₂') ∗ ((a + 88#64) ↦ₛ [d₂.fin]) ∗
      bytesIn d₂.ro (p + BitVec.ofNat 64 j) ((d₂.msg.drop j).take B) ∗
      ((a + 72#64) ↦ₛ buf₂) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗ ((a + 48#64) ↦ₛ d₂.pad) ∗
      ((a + 89#64) ↦ₛ d₂.rest) ∗ bytesIn d₂.ro p (d₂.msg.take j) ∗
      bytesIn d₂.ro (p + BitVec.ofNat 64 j + BitVec.ofNat 64 B) ((d₂.msg.drop j).drop B) ∗
      (T ↦₆₄ c₂.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ c₂.regs.regs 30#5) ∗ d₂.R = V₂
    have g1₁ : n₁' ⊨ ((T + 0x10#64) ↦₆₄ BitVec.ofNat 64 B) ∗
        (((T + 0x10#64 + 8#64) ↦₆₄ BitVec.ofNat 64 cc) ∗ V₁) :=
      Satisfies.of_eq h₁ (by rw [← hV₁]; simp only [Cells4]; ac_rfl)
    have g1₂ : n₂' ⊨ ((T + 0x10#64) ↦₆₄ BitVec.ofNat 64 B) ∗
        (((T + 0x10#64 + 8#64) ↦₆₄ BitVec.ofNat 64 cc) ∗ V₂) :=
      Satisfies.of_eq h₂ (by rw [← hV₂]; simp only [Cells4]; ac_rfl)
    have d2₁ := sat64_read g1₁
    have d2₂ := sat64_read g1₂
    have d3₁ := sat64_read (Satisfies.of_eq g1₁ (Q := ((T + 0x10#64 + 8#64) ↦₆₄ BitVec.ofNat 64 cc) ∗
      (((T + 0x10#64) ↦₆₄ BitVec.ofNat 64 B) ∗ V₁)))
    have d3₂ := sat64_read (Satisfies.of_eq g1₂ (Q := ((T + 0x10#64 + 8#64) ↦₆₄ BitVec.ofNat 64 cc) ∗
      (((T + 0x10#64) ↦₆₄ BitVec.ofNat 64 B) ∗ V₂)))
    refine rs hc hr₁ hr₂ (f_e8 hP k₁) (f_e8 hP k₂)
      (ex_ldp64_sp' 2#5 4#5 (by decide) (by decide) 0x10#64 hTal d2₁.2.1 d3₁.2.1 _ _ d2₁.1 d3₁.1)
      (ex_ldp64_sp' 2#5 4#5 (by decide) (by decide) 0x10#64 hTal d2₂.2.1 d3₂.2.1 _ _ d2₂.1 d3₂.1)
      (by simp [leakedValues, evalAddrMode]) ?_
    rw [pc4 pl.base 920 924]
    -- 924: add x18, x18, x2
    refine rs hc hr₁ hr₂ (f_ec hP k₁) (f_ec hP k₂)
      (ex_add_shift0' 18#5 18#5 2#5 (by decide) (by decide) (by decide)
        (p + BitVec.ofNat 64 (j + B)) (by simp [upd_apply, f18₁, pc_add]))
      (ex_add_shift0' 18#5 18#5 2#5 (by decide) (by decide) (by decide)
        (p + BitVec.ofNat 64 (j + B)) (by simp [upd_apply, f18₂, pc_add])) rfl ?_
    rw [pc4 pl.base 924 928]
    -- 928: sub x4, x4, x2
    have hsub : BitVec.ofNat 64 cc - BitVec.ofNat 64 B = BitVec.ofNat 64 (cc - B) :=
      ofNat_sub_ofNat cc B hc64 (by omega)
    refine rs hc hr₁ hr₂ (f_f0 hP k₁) (f_f0 hP k₂)
      (ex_sub_shift0' 4#5 4#5 2#5 (by decide) (by decide) (by decide)
        (BitVec.ofNat 64 (cc - B)) (by simp only [upd_apply]; simpa using hsub))
      (ex_sub_shift0' 4#5 4#5 2#5 (by decide) (by decide) (by decide)
        (BitVec.ofNat 64 (cc - B)) (by simp only [upd_apply]; simpa using hsub)) rfl ?_
    rw [pc4 pl.base 928 932]
    have kq₁ := (((kf₁.upd 2#5 (by decide) (BitVec.ofNat 64 B)).upd 4#5 (by decide)
      (BitVec.ofNat 64 cc)).upd 18#5 (by decide) (p + BitVec.ofNat 64 (j + B))).upd 4#5 (by decide)
      (BitVec.ofNat 64 (cc - B))
    have kq₂ := (((kf₂.upd 2#5 (by decide) (BitVec.ofNat 64 B)).upd 4#5 (by decide)
      (BitVec.ofNat 64 cc)).upd 18#5 (by decide) (p + BitVec.ofNat 64 (j + B))).upd 4#5 (by decide)
      (BitVec.ofNat 64 (cc - B))
    have hmf₁ : n₁' ⊨ Mem c₁ d₁ a p T 0#64 rh₁' buf₁ (BitVec.ofNat 64 B) (BitVec.ofNat 64 cc) := by
      simp only [Mem, Fields]
      rw [bytesIn_three d₁.ro p d₁.msg j B (by omega)]
      exact Satisfies.of_eq g1₁ (by rw [← hV₁]; simp only [Cells4]; ac_rfl)
    have hmf₂ : n₂' ⊨ Mem c₂ d₂ a p T 0#64 rh₂' buf₂ (BitVec.ofNat 64 B) (BitVec.ofNat 64 cc) := by
      simp only [Mem, Fields]
      rw [bytesIn_three d₂.ro p d₂.msg j B (by omega)]
      exact Satisfies.of_eq g1₂ (by rw [← hV₂]; simp only [Cells4]; ac_rfl)
    -- 932: cbz x4, 784
    refine rs hc hr₁ hr₂ (f_f4 hP k₁) (f_f4 hP k₂) (ex_cbz 4#5 (by decide) _)
      (ex_cbz 4#5 (by decide) _) rfl ?_
    rw [upd_same, upd_same]
    by_cases hcB : cc - B = 0
    · have e0 : BitVec.ofNat 64 (cc - B) = 0#64 := by rw [hcB]
      rw [if_pos e0]
      rw [show pl.base + 932#64 + 0xffffffffffffff6c#64 = pl.base + 784#64 by bv_omega]
      exact K784 _ _ _ _ _ _ rh₁' rh₂' buf₁ buf₂ 0#64 _ _ _ _ k₁ k₂ kq₁ kq₂ l₁ l₂ hb₁ hb₂
        (by rw [htgt]; simp; omega) hmf₁ hmf₂
    · have e0 : BitVec.ofNat 64 (cc - B) ≠ 0#64 := fun e => hcB ((ofNat_eq_zero _ (by omega)).mp e)
      rw [if_neg e0]
      rw [pc4 pl.base 932 936]
      -- 936: b 840
      refine rs hc hr₁ hr₂ (f_f8 hP k₁) (f_f8 hP k₂) (ex_b _) (ex_b _) rfl ?_
      rw [show pl.base + 936#64 + 0xffffffffffffffa0#64 = pl.base + 840#64 by bv_omega]
      exact seg840 hc hP hr₁ hr₂ K892 k₁ k₂ kq₁ kq₂ (j + B) (cc - B) (by omega) (by omega)
        (by rw [htgt]; omega) (by omega) (by omega) (by simp [upd_apply, f0₁])
        (by simp [upd_apply, f0₂]) (by simp [upd_apply]) (by simp [upd_apply]) (by simp [upd_apply])
        (by simp [upd_apply]) l₁ l₂ hb₁ hb₂ hmf₁ hmf₂

end seg

end Poly1305DebianCtUpdate

end
end

section
section
/-! # `poly1305_update`, text offsets 716–824 in both runs: "handle leftover"

With `L = leftover` in `1..15` (the same in both runs, it is public): `w = min (16 - L, n)` bytes
of the message go into the buffer at `L`; if the buffer is then full (`L + w = 16`) both runs call
`poly1305_blocks` on it (`call2`), store `leftover = 0` and go on at 828 (`seg828`); otherwise
`leftover = L + n` and both return (epilogue at 784). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtUpdate

open Arm64 Arm64.Obj Poly1305DebianCt Leakage Poly1305DebianCtFw
open Poly1305Libsodium (u64At bytesIn)

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_str64_sp' (a : BitVec 5) (ha : a ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hw : m.canWrite (sp + off) 8 = true) (val : BitVec 64)
    (hv : r a = val) :
    execInstWithSvc svc (.str .X64 (.gpr a) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) r sp ps (m.write64 (sp + off) val) v := by
  rw [ex_str64_sp a ha off hal hw, hv]

theorem ex_ldr64_sp' (a : BitVec 5) (ha : a ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hr : m.canRead (sp + off) 8 = true) (val : BitVec 64)
    (hv : m.read64 (sp + off) = val) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr a) (.Offset .sp off)) (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd r a val) sp ps m v := by
  rw [ex_ldr64_sp a ha off hal hr, hv]

end exec

section seg

variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

set_option maxHeartbeats 8000000 in
/-- From offset 768 (`add x6, x6, x1`), with `w` bytes copied into the buffer at `L`. -/
theorem seg768 (hc : StopCompat stop₁ stop₂) (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {c₁ c₂ : State} (hr₁ : c₁.status = .Running) (hr₂ : c₂.status = .Running)
    {d₁ d₂ : RunD} {a p T : BitVec 64} {tgt : Nat}
    (K784 : ExitK2 pl X stop₁ stop₂ c₁ c₂ d₁ d₂ (pl.base + 784#64) a p T tgt)
    (K892 : ExitK2 pl X stop₁ stop₂ c₁ c₂ d₁ d₂ (pl.base + 892#64) a p T tgt)
    (hTal : T &&& 0b1111#64 = 0#64)
    {r₁ r₂ : BitVec 5 → BitVec 64} {ps₁ ps₂ : PState} {m₁ m₂ : Memory}
    (hcl₁ : (P pl X).CodeLoaded m₁) (hcl₂ : (P pl X).CodeLoaded m₂)
    (hk₁ : Kept r₁ c₁.regs.regs) (hk₂ : Kept r₂ c₂.regs.regs)
    (L n w : Nat) (hL0 : 0 < L) (hL16 : L < 16) (hn64 : n < 2 ^ 64) (hw : w = min (16 - L) n)
    (htgt : tgt = (L + n) % 16)
    (hlen₁ : d₁.msg.length = n) (hlen₂ : d₂.msg.length = n)
    (h0₁ : r₁ 0#5 = a) (h0₂ : r₂ 0#5 = a)
    (h1₁ : r₁ 1#5 = BitVec.ofNat 64 w) (h1₂ : r₂ 1#5 = BitVec.ofNat 64 w)
    (h6₁ : r₁ 6#5 = BitVec.ofNat 64 L) (h6₂ : r₂ 6#5 = BitVec.ofNat 64 L)
    (h18₁ : r₁ 18#5 = p) (h18₂ : r₂ 18#5 = p)
    (h4₁ : r₁ 4#5 = BitVec.ofNat 64 n) (h4₂ : r₂ 4#5 = BitVec.ofNat 64 n)
    {rh₁ rh₂ buf₁ buf₂ : List (BitVec 8)} (hrh₁ : rh₁.length = 48) (hrh₂ : rh₂.length = 48)
    (hb₁ : buf₁.length = 16) (hb₂ : buf₂.length = 16) {u2₁ u3₁ u2₂ u3₂ : BitVec 64}
    (hm₁ : m₁ ⊨ Mem c₁ d₁ a p T (BitVec.ofNat 64 L) rh₁ buf₁ u2₁ u3₁)
    (hm₂ : m₂ ⊨ Mem c₂ d₂ a p T (BitVec.ofNat 64 L) rh₂ buf₂ u2₂ u3₂) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 768#64) r₁ T ps₁ m₁ c₁.vregs.regs)
      (mkS c₂ (pl.base + 768#64) r₂ T ps₂ m₂ c₂.vregs.regs) := by
  have hLw : L + w ≤ 16 := by omega
  -- 768: add x6, x6, x1
  have hadd : BitVec.ofNat 64 L + BitVec.ofNat 64 w = BitVec.ofNat 64 (L + w) :=
    (BitVec.ofNat_add L w).symm
  refine rs hc hr₁ hr₂ (f_50 hP hcl₁) (f_50 hP hcl₂)
    (ex_add_shift0' 6#5 6#5 1#5 (by decide) (by decide) (by decide) _ (by rw [h6₁, h1₁, hadd]))
    (ex_add_shift0' 6#5 6#5 1#5 (by decide) (by decide) (by decide) _ (by rw [h6₂, h1₂, hadd]))
    rfl ?_
  rw [pc4 pl.base 768 772]
  -- 772: str x6, [x0, #0x40]
  generalize hW₁ : (a ↦ₛ rh₁) ∗ ((a + 88#64) ↦ₛ [d₁.fin]) ∗ ((a + 48#64) ↦ₛ d₁.pad) ∗
    ((a + 89#64) ↦ₛ d₁.rest) ∗ bytesIn d₁.ro p d₁.msg ∗
    Cells4 T (c₁.regs.regs 29#5) (c₁.regs.regs 30#5) u2₁ u3₁ ∗ d₁.R = W₁
  generalize hW₂ : (a ↦ₛ rh₂) ∗ ((a + 88#64) ↦ₛ [d₂.fin]) ∗ ((a + 48#64) ↦ₛ d₂.pad) ∗
    ((a + 89#64) ↦ₛ d₂.rest) ∗ bytesIn d₂.ro p d₂.msg ∗
    Cells4 T (c₂.regs.regs 29#5) (c₂.regs.regs 30#5) u2₂ u3₂ ∗ d₂.R = W₂
  have hm1₁ : m₁ ⊨ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 L) ∗ (((a + 72#64) ↦ₛ buf₁) ∗ W₁) :=
    Satisfies.of_eq hm₁ (by rw [← hW₁]; simp only [Mem, Fields]; ac_rfl)
  have hm1₂ : m₂ ⊨ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 L) ∗ (((a + 72#64) ↦ₛ buf₂) ∗ W₂) :=
    Satisfies.of_eq hm₂ (by rw [← hW₂]; simp only [Mem, Fields]; ac_rfl)
  have c0₁ := sat64_read hm1₁
  have c0₂ := sat64_read hm1₂
  refine rsw hc hr₁ hr₂ hcl₁ hcl₂ (f_54 hP hcl₁) (f_54 hP hcl₂)
    (ex_str64_gpr' 6#5 0#5 (by decide) (by decide) _ _ (BitVec.ofNat 64 (L + w))
      (by rw [upd_ne _ _ (by decide), h0₁]) (upd_same _ _ _) c0₁.2.2)
    (ex_str64_gpr' 6#5 0#5 (by decide) (by decide) _ _ (BitVec.ofNat 64 (L + w))
      (by rw [upd_ne _ _ (by decide), h0₂]) (upd_same _ _ _) c0₂.2.2)
    (by simp [leakedValues, evalAddrMode, h0₁, h0₂]) ?_
  intro k₁ k₂
  rw [pc4 pl.base 772 776]
  have w1₁ := sat64_write hm1₁ (BitVec.ofNat 64 (L + w))
  have w1₂ := sat64_write hm1₂ (BitVec.ofNat 64 (L + w))
  generalize m₁.write64 (a + 64#64) (BitVec.ofNat 64 (L + w)) = n₁ at w1₁ k₁ ⊢
  generalize m₂.write64 (a + 64#64) (BitVec.ofNat 64 (L + w)) = n₂ at w1₂ k₂ ⊢
  simp only [mkS_mem] at k₁ k₂
  -- 776: cmp x6, #15
  refine rs hc hr₁ hr₂ (f_58 hP k₁) (f_58 hP k₂) (ex_cmp_imm' 6#5 (by decide) _ _ (upd_same _ _ _))
    (ex_cmp_imm' 6#5 (by decide) _ _ (upd_same _ _ _)) rfl ?_
  rw [pc4 pl.base 776 780]
  -- 780: b.hi 796
  refine rs hc hr₁ hr₂ (f_5c hP k₁) (f_5c hP k₂) (ex_bcond _ _) (ex_bcond _ _) rfl ?_
  rw [hi15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have kk₁ := hk₁.upd 6#5 (by decide) (BitVec.ofNat 64 (L + w))
  have kk₂ := hk₂.upd 6#5 (by decide) (BitVec.ofNat 64 (L + w))
  by_cases hfull : 15 < L + w
  swap
  · -- the buffer is not full: return
    simp only [hfull, decide_false, Bool.false_eq_true, if_false]
    rw [pc4 pl.base 780 784]
    have hwn : w = n := by omega
    exact K784 _ _ _ _ n₁ n₂ rh₁ rh₂ buf₁ buf₂ (BitVec.ofNat 64 (L + w)) u2₁ u3₁ u2₂ u3₂ k₁ k₂ kk₁ kk₂
      hrh₁ hrh₂ hb₁ hb₂ (by rw [htgt]; simp; omega)
      (Satisfies.of_eq w1₁ (by rw [← hW₁]; simp only [Mem, Fields]; ac_rfl))
      (Satisfies.of_eq w1₂ (by rw [← hW₂]; simp only [Mem, Fields]; ac_rfl))
  · -- the buffer is full: absorb it
    simp only [hfull, decide_true, if_true]
    rw [show pl.base + 780#64 + 0x0000000000000010#64 = pl.base + 796#64 by bv_omega]
    have hw16 : L + w = 16 := by omega
    have hwn : w ≤ n := by omega
    have hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 w = BitVec.ofNat 64 (n - w) :=
      ofNat_sub_ofNat n w hn64 hwn
    -- 796: sub x4, x4, x1
    refine rs hc hr₁ hr₂ (f_6c hP k₁) (f_6c hP k₂)
      (ex_sub_shift0' 4#5 4#5 1#5 (by decide) (by decide) (by decide) (BitVec.ofNat 64 (n - w))
        (by simp only [upd_apply]; simpa [h4₁, h1₁] using hsub))
      (ex_sub_shift0' 4#5 4#5 1#5 (by decide) (by decide) (by decide) (BitVec.ofNat 64 (n - w))
        (by simp only [upd_apply]; simpa [h4₂, h1₂] using hsub)) rfl ?_
    rw [pc4 pl.base 796 800]
    -- 800: add x18, x18, x1
    refine rs hc hr₁ hr₂ (f_70 hP k₁) (f_70 hP k₂)
      (ex_add_shift0' 18#5 18#5 1#5 (by decide) (by decide) (by decide) (p + BitVec.ofNat 64 w)
        (by simp [upd_apply, h18₁, h1₁]))
      (ex_add_shift0' 18#5 18#5 1#5 (by decide) (by decide) (by decide) (p + BitVec.ofNat 64 w)
        (by simp [upd_apply, h18₂, h1₂])) rfl ?_
    rw [pc4 pl.base 800 804]
    -- 804: mov x2, #16
    refine rs hc hr₁ hr₂ (f_74 hP k₁) (f_74 hP k₂) (ex_movz64' 2#5 (by decide) _ 16#64 rfl)
      (ex_movz64' 2#5 (by decide) _ 16#64 rfl) rfl ?_
    rw [pc4 pl.base 804 808]
    -- 808: add x1, x0, #0x48
    refine rs hc hr₁ hr₂ (f_78 hP k₁) (f_78 hP k₂)
      (ex_add_imm' 1#5 0#5 (by decide) (by decide) _ (a + 72#64) (by simp [upd_apply, h0₁] <;> rfl))
      (ex_add_imm' 1#5 0#5 (by decide) (by decide) _ (a + 72#64) (by simp [upd_apply, h0₂] <;> rfl))
      rfl ?_
    rw [pc4 pl.base 808 812]
    have e0₁ : upd (upd (upd (upd (upd r₁ 6#5 (BitVec.ofNat 64 (L + w))) 4#5
        (BitVec.ofNat 64 (n - w))) 18#5 (p + BitVec.ofNat 64 w)) 2#5 16#64) 1#5 (a + 72#64) 0#5 = a := by
      simp [upd_apply, h0₁]
    have e0₂ : upd (upd (upd (upd (upd r₂ 6#5 (BitVec.ofNat 64 (L + w))) 4#5
        (BitVec.ofNat 64 (n - w))) 18#5 (p + BitVec.ofNat 64 w)) 2#5 16#64) 1#5 (a + 72#64) 0#5 = a := by
      simp [upd_apply, h0₂]
    have e1₁ : upd (upd (upd (upd (upd r₁ 6#5 (BitVec.ofNat 64 (L + w))) 4#5
        (BitVec.ofNat 64 (n - w))) 18#5 (p + BitVec.ofNat 64 w)) 2#5 16#64) 1#5 (a + 72#64) 1#5 =
        a + 72#64 := by simp [upd_apply]
    have e1₂ : upd (upd (upd (upd (upd r₂ 6#5 (BitVec.ofNat 64 (L + w))) 4#5
        (BitVec.ofNat 64 (n - w))) 18#5 (p + BitVec.ofNat 64 w)) 2#5 16#64) 1#5 (a + 72#64) 1#5 =
        a + 72#64 := by simp [upd_apply]
    have e2₁ : upd (upd (upd (upd (upd r₁ 6#5 (BitVec.ofNat 64 (L + w))) 4#5
        (BitVec.ofNat 64 (n - w))) 18#5 (p + BitVec.ofNat 64 w)) 2#5 16#64) 1#5 (a + 72#64) 2#5 =
        16#64 := by simp [upd_apply]
    have e2₂ : upd (upd (upd (upd (upd r₂ 6#5 (BitVec.ofNat 64 (L + w))) 4#5
        (BitVec.ofNat 64 (n - w))) 18#5 (p + BitVec.ofNat 64 w)) 2#5 16#64) 1#5 (a + 72#64) 2#5 =
        16#64 := by simp [upd_apply]
    have e4₁ : upd (upd (upd (upd (upd r₁ 6#5 (BitVec.ofNat 64 (L + w))) 4#5
        (BitVec.ofNat 64 (n - w))) 18#5 (p + BitVec.ofNat 64 w)) 2#5 16#64) 1#5 (a + 72#64) 4#5 =
        BitVec.ofNat 64 (n - w) := by simp [upd_apply]
    have e4₂ : upd (upd (upd (upd (upd r₂ 6#5 (BitVec.ofNat 64 (L + w))) 4#5
        (BitVec.ofNat 64 (n - w))) 18#5 (p + BitVec.ofNat 64 w)) 2#5 16#64) 1#5 (a + 72#64) 4#5 =
        BitVec.ofNat 64 (n - w) := by simp [upd_apply]
    have e18₁ : upd (upd (upd (upd (upd r₁ 6#5 (BitVec.ofNat 64 (L + w))) 4#5
        (BitVec.ofNat 64 (n - w))) 18#5 (p + BitVec.ofNat 64 w)) 2#5 16#64) 1#5 (a + 72#64) 18#5 =
        p + BitVec.ofNat 64 w := by simp [upd_apply]
    have e18₂ : upd (upd (upd (upd (upd r₂ 6#5 (BitVec.ofNat 64 (L + w))) 4#5
        (BitVec.ofNat 64 (n - w))) 18#5 (p + BitVec.ofNat 64 w)) 2#5 16#64) 1#5 (a + 72#64) 18#5 =
        p + BitVec.ofNat 64 w := by simp [upd_apply]
    have kR₁ := (((kk₁.upd 4#5 (by decide) (BitVec.ofNat 64 (n - w))).upd 18#5 (by decide)
      (p + BitVec.ofNat 64 w)).upd 2#5 (by decide) 16#64).upd 1#5 (by decide) (a + 72#64)
    have kR₂ := (((kk₂.upd 4#5 (by decide) (BitVec.ofNat 64 (n - w))).upd 18#5 (by decide)
      (p + BitVec.ofNat 64 w)).upd 2#5 (by decide) 16#64).upd 1#5 (by decide) (a + 72#64)
    generalize upd (upd (upd (upd (upd r₁ 6#5 (BitVec.ofNat 64 (L + w))) 4#5
        (BitVec.ofNat 64 (n - w))) 18#5 (p + BitVec.ofNat 64 w)) 2#5 16#64) 1#5 (a + 72#64) = R₁
      at e0₁ e1₁ e2₁ e4₁ e18₁ kR₁ ⊢
    generalize upd (upd (upd (upd (upd r₂ 6#5 (BitVec.ofNat 64 (L + w))) 4#5
        (BitVec.ofNat 64 (n - w))) 18#5 (p + BitVec.ofNat 64 w)) 2#5 16#64) 1#5 (a + 72#64) = R₂
      at e0₂ e1₂ e2₂ e4₂ e18₂ kR₂ ⊢
    -- 812: str x4, [sp, #16]
    rw [← hW₁] at w1₁
    rw [← hW₂] at w1₂
    have hm4₁ : n₁ ⊨ ((T + 0x10#64) ↦₆₄ u2₁) ∗ ((a ↦ₛ rh₁) ∗ ((a + 88#64) ↦ₛ [d₁.fin]) ∗
        bytesIn false (a + 72#64) buf₁ ∗
        (((a + 64#64) ↦₆₄ BitVec.ofNat 64 (L + w)) ∗ ((a + 48#64) ↦ₛ d₁.pad) ∗
          ((a + 89#64) ↦ₛ d₁.rest) ∗ bytesIn d₁.ro p d₁.msg ∗ (T ↦₆₄ c₁.regs.regs 29#5) ∗
          ((T + 8#64) ↦₆₄ c₁.regs.regs 30#5) ∗ ((T + 0x10#64 + 8#64) ↦₆₄ u3₁) ∗ d₁.R)) :=
      Satisfies.of_eq w1₁ (by simp only [Cells4, bytesIn, Bool.false_eq_true, if_false]; ac_rfl)
    have hm4₂ : n₂ ⊨ ((T + 0x10#64) ↦₆₄ u2₂) ∗ ((a ↦ₛ rh₂) ∗ ((a + 88#64) ↦ₛ [d₂.fin]) ∗
        bytesIn false (a + 72#64) buf₂ ∗
        (((a + 64#64) ↦₆₄ BitVec.ofNat 64 (L + w)) ∗ ((a + 48#64) ↦ₛ d₂.pad) ∗
          ((a + 89#64) ↦ₛ d₂.rest) ∗ bytesIn d₂.ro p d₂.msg ∗ (T ↦₆₄ c₂.regs.regs 29#5) ∗
          ((T + 8#64) ↦₆₄ c₂.regs.regs 30#5) ∗ ((T + 0x10#64 + 8#64) ↦₆₄ u3₂) ∗ d₂.R)) :=
      Satisfies.of_eq w1₂ (by simp only [Cells4, bytesIn, Bool.false_eq_true, if_false]; ac_rfl)
    have c4₁ := sat64_read hm4₁
    have c4₂ := sat64_read hm4₂
    refine rsw hc hr₁ hr₂ k₁ k₂ (f_7c hP k₁) (f_7c hP k₂)
      (ex_str64_sp' 4#5 (by decide) 0x10#64 hTal c4₁.2.2 _ e4₁)
      (ex_str64_sp' 4#5 (by decide) 0x10#64 hTal c4₂.2.2 _ e4₂)
      (by simp [leakedValues, evalAddrMode]) ?_
    intro k5₁ k5₂
    rw [pc4 pl.base 812 816]
    have hm5₁ := sat64_write hm4₁ (BitVec.ofNat 64 (n - w))
    have hm5₂ := sat64_write hm4₂ (BitVec.ofNat 64 (n - w))
    generalize n₁.write64 (T + 0x10#64) (BitVec.ofNat 64 (n - w)) = n5₁ at hm5₁ k5₁ ⊢
    generalize n₂.write64 (T + 0x10#64) (BitVec.ofNat 64 (n - w)) = n5₂ at hm5₂ k5₂ ⊢
    simp only [mkS_mem] at k5₁ k5₂
    -- 816: bl poly1305_blocks
    refine call2 (F₁ := ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (L + w)) ∗ ((a + 48#64) ↦ₛ d₁.pad) ∗
          ((a + 89#64) ↦ₛ d₁.rest) ∗ bytesIn d₁.ro p d₁.msg ∗
          Cells4 T (c₁.regs.regs 29#5) (c₁.regs.regs 30#5) (BitVec.ofNat 64 (n - w)) u3₁ ∗ d₁.R)
      (F₂ := ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (L + w)) ∗ ((a + 48#64) ↦ₛ d₂.pad) ∗
          ((a + 89#64) ↦ₛ d₂.rest) ∗ bytesIn d₂.ro p d₂.msg ∗
          Cells4 T (c₂.regs.regs 29#5) (c₂.regs.regs 30#5) (BitVec.ofNat 64 (n - w)) u3₂ ∗ d₂.R)
      (ro₁ := false) (ro₂ := false) (fin₁ := d₁.fin) (fin₂ := d₂.fin) (msg₁ := buf₁) (msg₂ := buf₂)
      (rh₁ := rh₁) (rh₂ := rh₂)
      hc hP hr₁ hr₂ k5₁ k5₂ (f_80 hP k5₁) (f_80 hP k5₂) (by bv_omega)
      (e0₁.trans e0₂.symm) (e1₁.trans e1₂.symm) (e2₁.trans e2₂.symm) hrh₁ hrh₂
      (by rw [e2₁, hb₁]; rfl) (by rw [e2₂, hb₂]; rfl) (by omega) (by omega)
      (by rw [e0₁, e1₁]; exact Satisfies.of_eq hm5₁ (by simp only [Cells4]; ac_rfl))
      (by rw [e0₂, e1₂]; exact Satisfies.of_eq hm5₂ (by simp only [Cells4]; ac_rfl)) ?_
    intro n₁' n₂' ps₁' ps₂' q₁ q₂ rh₁' rh₂' k₁' k₂' l₁ l₂ h₁ h₂
    rw [e0₁, e1₁] at h₁
    rw [e0₂, e1₂] at h₂
    rw [pc4 pl.base 816 820]
    have f0₁ : (Poly1305DebianCtBlocks.mkRegs ⟨upd R₁ 30#5 (pl.base + 820#64)⟩ q₁).regs 0#5 = a := by
      rw [mkRegs_out _ _ _ (by decide), upd_ne _ _ (by decide), e0₁]
    have f0₂ : (Poly1305DebianCtBlocks.mkRegs ⟨upd R₂ 30#5 (pl.base + 820#64)⟩ q₂).regs 0#5 = a := by
      rw [mkRegs_out _ _ _ (by decide), upd_ne _ _ (by decide), e0₂]
    have f18₁ : (Poly1305DebianCtBlocks.mkRegs ⟨upd R₁ 30#5 (pl.base + 820#64)⟩ q₁).regs 18#5 =
        p + BitVec.ofNat 64 w := by
      rw [mkRegs_out _ _ _ (by decide), upd_ne _ _ (by decide), e18₁]
    have f18₂ : (Poly1305DebianCtBlocks.mkRegs ⟨upd R₂ 30#5 (pl.base + 820#64)⟩ q₂).regs 18#5 =
        p + BitVec.ofNat 64 w := by
      rw [mkRegs_out _ _ _ (by decide), upd_ne _ _ (by decide), e18₂]
    have kf₁ := (kR₁.upd 30#5 (by decide) (pl.base + 820#64)).mkRegs q₁
    have kf₂ := (kR₂.upd 30#5 (by decide) (pl.base + 820#64)).mkRegs q₂
    generalize (Poly1305DebianCtBlocks.mkRegs ⟨upd R₁ 30#5 (pl.base + 820#64)⟩ q₁).regs = Q₁
      at f0₁ f18₁ kf₁ ⊢
    generalize (Poly1305DebianCtBlocks.mkRegs ⟨upd R₂ 30#5 (pl.base + 820#64)⟩ q₂).regs = Q₂
      at f0₂ f18₂ kf₂ ⊢
    -- 820: str xzr, [x0, #0x40]
    generalize hG₁ : ((a + 48#64) ↦ₛ d₁.pad) ∗ ((a + 89#64) ↦ₛ d₁.rest) ∗ bytesIn d₁.ro p d₁.msg ∗
      Cells4 T (c₁.regs.regs 29#5) (c₁.regs.regs 30#5) (BitVec.ofNat 64 (n - w)) u3₁ ∗ d₁.R = G₁
      at h₁
    generalize hG₂ : ((a + 48#64) ↦ₛ d₂.pad) ∗ ((a + 89#64) ↦ₛ d₂.rest) ∗ bytesIn d₂.ro p d₂.msg ∗
      Cells4 T (c₂.regs.regs 29#5) (c₂.regs.regs 30#5) (BitVec.ofNat 64 (n - w)) u3₂ ∗ d₂.R = G₂
      at h₂
    have g1₁ : n₁' ⊨ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (L + w)) ∗
        ((a ↦ₛ rh₁') ∗ ((a + 88#64) ↦ₛ [d₁.fin]) ∗ bytesIn false (a + 72#64) buf₁ ∗ G₁) :=
      Satisfies.of_eq h₁
    have g1₂ : n₂' ⊨ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 (L + w)) ∗
        ((a ↦ₛ rh₂') ∗ ((a + 88#64) ↦ₛ [d₂.fin]) ∗ bytesIn false (a + 72#64) buf₂ ∗ G₂) :=
      Satisfies.of_eq h₂
    have d0₁ := sat64_read g1₁
    have d0₂ := sat64_read g1₂
    refine rsw hc hr₁ hr₂ k₁' k₂' (f_84 hP k₁') (f_84 hP k₂')
      (ex_str64_xzr' 0#5 (by decide) _ _ (by rw [f0₁]) d0₁.2.2)
      (ex_str64_xzr' 0#5 (by decide) _ _ (by rw [f0₂]) d0₂.2.2)
      (by simp [leakedValues, evalAddrMode, f0₁, f0₂]) ?_
    intro k8₁ k8₂
    rw [pc4 pl.base 820 824]
    have g2₁ := sat64_write g1₁ 0#64
    have g2₂ := sat64_write g1₂ 0#64
    generalize n₁'.write64 (a + 64#64) 0#64 = n8₁ at g2₁ k8₁ ⊢
    generalize n₂'.write64 (a + 64#64) 0#64 = n8₂ at g2₂ k8₂ ⊢
    simp only [mkS_mem] at k8₁ k8₂
    -- 824: ldr x4, [sp, #16]
    rw [← hG₁] at g2₁
    rw [← hG₂] at g2₂
    have g3₁ : n8₁ ⊨ ((T + 0x10#64) ↦₆₄ BitVec.ofNat 64 (n - w)) ∗
        (Fields a rh₁' d₁.pad 0#64 buf₁ d₁.fin d₁.rest ∗ bytesIn d₁.ro p d₁.msg ∗
          (T ↦₆₄ c₁.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ c₁.regs.regs 30#5) ∗
          ((T + 0x10#64 + 8#64) ↦₆₄ u3₁) ∗ d₁.R) :=
      Satisfies.of_eq g2₁ (by simp only [Fields, Cells4, bytesIn, Bool.false_eq_true, if_false]; ac_rfl)
    have g3₂ : n8₂ ⊨ ((T + 0x10#64) ↦₆₄ BitVec.ofNat 64 (n - w)) ∗
        (Fields a rh₂' d₂.pad 0#64 buf₂ d₂.fin d₂.rest ∗ bytesIn d₂.ro p d₂.msg ∗
          (T ↦₆₄ c₂.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ c₂.regs.regs 30#5) ∗
          ((T + 0x10#64 + 8#64) ↦₆₄ u3₂) ∗ d₂.R) :=
      Satisfies.of_eq g2₂ (by simp only [Fields, Cells4, bytesIn, Bool.false_eq_true, if_false]; ac_rfl)
    have d1₁ := sat64_read g3₁
    have d1₂ := sat64_read g3₂
    refine rs hc hr₁ hr₂ (f_88 hP k8₁) (f_88 hP k8₂)
      (ex_ldr64_sp' 4#5 (by decide) 0x10#64 hTal d1₁.2.1 _ d1₁.1)
      (ex_ldr64_sp' 4#5 (by decide) 0x10#64 hTal d1₂.2.1 _ d1₂.1)
      (by simp [leakedValues, evalAddrMode]) ?_
    rw [pc4 pl.base 824 828]
    -- 828: the whole blocks of the rest
    exact seg828 hc hP hr₁ hr₂ K784 K892 hTal k8₁ k8₂ (kf₁.upd 4#5 (by decide) _)
      (kf₂.upd 4#5 (by decide) _) w (n - w) (by rw [htgt]; omega) (by omega) (by omega) (by omega)
      (by rw [upd_ne _ _ (by decide), f0₁]) (by rw [upd_ne _ _ (by decide), f0₂])
      (by rw [upd_ne _ _ (by decide), f18₁]) (by rw [upd_ne _ _ (by decide), f18₂])
      (upd_same _ _ _) (upd_same _ _ _) l₁ l₂ hb₁ hb₂
      (Satisfies.of_eq g3₁ (by simp only [Mem, Cells4]; ac_rfl))
      (Satisfies.of_eq g3₂ (by simp only [Mem, Cells4]; ac_rfl))

end seg

end Poly1305DebianCtUpdate

end
end

section
section
/-! # `poly1305_update`, text offsets 716–764 in both runs: `w = min (16 - L, n)` bytes into the
buffer at `L` -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtUpdate

open Arm64 Arm64.Obj Poly1305DebianCt Leakage Poly1305DebianCtFw
open Poly1305Libsodium (u64At bytesIn)

theorem csel_w (L n : Nat) (hL : L < 16) (hn : n < 2 ^ 64) :
    (if ConditionHolds .LS (AddWithCarry64 (BitVec.ofNat 64 (16 - L)) (~~~(BitVec.ofNat 64 n))
      true).2 = true then BitVec.ofNat 64 (16 - L) else BitVec.ofNat 64 n) =
      BitVec.ofNat 64 (min (16 - L) n) := by
  rw [ls_cmp, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt hn]
  by_cases h : 16 - L ≤ n
  · simp [h, Nat.min_eq_left h]
  · simp [h, Nat.min_eq_right (by omega : n ≤ 16 - L)]

section seg

variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

set_option maxHeartbeats 8000000 in
theorem seg716 (hc : StopCompat stop₁ stop₂) (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {c₁ c₂ : State} (hr₁ : c₁.status = .Running) (hr₂ : c₂.status = .Running)
    {d₁ d₂ : RunD} {a p T : BitVec 64} {tgt : Nat}
    (K784 : ExitK2 pl X stop₁ stop₂ c₁ c₂ d₁ d₂ (pl.base + 784#64) a p T tgt)
    (K892 : ExitK2 pl X stop₁ stop₂ c₁ c₂ d₁ d₂ (pl.base + 892#64) a p T tgt)
    (hTal : T &&& 0b1111#64 = 0#64)
    {r₁ r₂ : BitVec 5 → BitVec 64} {ps₁ ps₂ : PState} {m₁ m₂ : Memory}
    (hcl₁ : (P pl X).CodeLoaded m₁) (hcl₂ : (P pl X).CodeLoaded m₂)
    (hk₁ : Kept r₁ c₁.regs.regs) (hk₂ : Kept r₂ c₂.regs.regs)
    (L n : Nat) (hL0 : 0 < L) (hL16 : L < 16) (hn64 : n < 2 ^ 64) (htgt : tgt = (L + n) % 16)
    (hlen₁ : d₁.msg.length = n) (hlen₂ : d₂.msg.length = n)
    (h0₁ : r₁ 0#5 = a) (h0₂ : r₂ 0#5 = a)
    (h2₁ : r₁ 2#5 = BitVec.ofNat 64 n) (h2₂ : r₂ 2#5 = BitVec.ofNat 64 n)
    (h6₁ : r₁ 6#5 = BitVec.ofNat 64 L) (h6₂ : r₂ 6#5 = BitVec.ofNat 64 L)
    (h18₁ : r₁ 18#5 = p) (h18₂ : r₂ 18#5 = p)
    (h4₁ : r₁ 4#5 = BitVec.ofNat 64 n) (h4₂ : r₂ 4#5 = BitVec.ofNat 64 n)
    {rh₁ rh₂ buf₁ buf₂ : List (BitVec 8)} (hrh₁ : rh₁.length = 48) (hrh₂ : rh₂.length = 48)
    (hb₁ : buf₁.length = 16) (hb₂ : buf₂.length = 16) {u2₁ u3₁ u2₂ u3₂ : BitVec 64}
    (hm₁ : m₁ ⊨ Mem c₁ d₁ a p T (BitVec.ofNat 64 L) rh₁ buf₁ u2₁ u3₁)
    (hm₂ : m₂ ⊨ Mem c₂ d₂ a p T (BitVec.ofNat 64 L) rh₂ buf₂ u2₂ u3₂) :
    ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ (pl.base + 716#64) r₁ T ps₁ m₁ c₁.vregs.regs)
      (mkS c₂ (pl.base + 716#64) r₂ T ps₂ m₂ c₂.vregs.regs) := by
  obtain ⟨w, hw⟩ : ∃ w, min (16 - L) n = w := ⟨_, rfl⟩
  have hsub : (16#64 : BitVec 64) - BitVec.ofNat 64 L = BitVec.ofNat 64 (16 - L) :=
    ofNat_sub_ofNat 16 L (by norm_num) (by omega)
  -- 716: mov x1, #16
  refine rs hc hr₁ hr₂ (f_1c hP hcl₁) (f_1c hP hcl₂) (ex_movz64' 1#5 (by decide) _ 16#64 rfl)
    (ex_movz64' 1#5 (by decide) _ 16#64 rfl) rfl ?_
  rw [pc4 pl.base 716 720]
  -- 720: sub x1, x1, x6
  refine rs hc hr₁ hr₂ (f_20 hP hcl₁) (f_20 hP hcl₂)
    (ex_sub_shift0' 1#5 1#5 6#5 (by decide) (by decide) (by decide) _
      (by rw [upd_same, upd_ne _ _ (by decide), h6₁, hsub]))
    (ex_sub_shift0' 1#5 1#5 6#5 (by decide) (by decide) (by decide) _
      (by rw [upd_same, upd_ne _ _ (by decide), h6₂, hsub])) rfl ?_
  rw [pc4 pl.base 720 724]
  -- 724: cmp x1, x2
  refine rs hc hr₁ hr₂ (f_24 hP hcl₁) (f_24 hP hcl₂)
    (ex_cmp_reg' 1#5 2#5 (by decide) (by decide) _ (BitVec.ofNat 64 n) (upd_same _ _ _) (by simp [upd_apply, h2₁]))
    (ex_cmp_reg' 1#5 2#5 (by decide) (by decide) _ (BitVec.ofNat 64 n) (upd_same _ _ _) (by simp [upd_apply, h2₂]))
    rfl ?_
  rw [pc4 pl.base 724 728]
  -- 728: csel x1, x1, x2, ls
  have e2₁ : upd (upd r₁ 1#5 16#64) 1#5 (BitVec.ofNat 64 (16 - L)) 2#5 = BitVec.ofNat 64 n := by
    simp [upd_apply, h2₁]
  have e2₂ : upd (upd r₂ 1#5 16#64) 1#5 (BitVec.ofNat 64 (16 - L)) 2#5 = BitVec.ofNat 64 n := by
    simp [upd_apply, h2₂]
  refine rs hc hr₁ hr₂ (f_28 hP hcl₁) (f_28 hP hcl₂)
    (ex_csel' .LS 1#5 1#5 2#5 (by decide) (by decide) (by decide) (BitVec.ofNat 64 w)
      (by rw [e2₁, upd_same, ← hw]; exact csel_w L n hL16 hn64))
    (ex_csel' .LS 1#5 1#5 2#5 (by decide) (by decide) (by decide) (BitVec.ofNat 64 w)
      (by rw [e2₂, upd_same, ← hw]; exact csel_w L n hL16 hn64)) rfl ?_
  rw [pc4 pl.base 728 732]
  have kk₁ := ((hk₁.upd 1#5 (by decide) 16#64).upd 1#5 (by decide) (BitVec.ofNat 64 (16 - L))).upd
    1#5 (by decide) (BitVec.ofNat 64 w)
  have kk₂ := ((hk₂.upd 1#5 (by decide) 16#64).upd 1#5 (by decide) (BitVec.ofNat 64 (16 - L))).upd
    1#5 (by decide) (BitVec.ofNat 64 w)
  -- 732: cbz x1, 768
  refine rs hc hr₁ hr₂ (f_2c hP hcl₁) (f_2c hP hcl₂) (ex_cbz 1#5 (by decide) _)
    (ex_cbz 1#5 (by decide) _) rfl ?_
  rw [upd_same, upd_same]
  by_cases hw0 : w = 0
  · have e0 : BitVec.ofNat 64 w = 0#64 := by rw [hw0]
    rw [if_pos e0, show pl.base + 732#64 + 0x0000000000000024#64 = pl.base + 768#64 by bv_omega]
    exact seg768 hc hP hr₁ hr₂ K784 K892 hTal hcl₁ hcl₂ kk₁ kk₂ L n w hL0 hL16 hn64 hw.symm htgt
      hlen₁ hlen₂ (by simp [upd_apply, h0₁]) (by simp [upd_apply, h0₂]) (upd_same _ _ _)
      (upd_same _ _ _) (by simp [upd_apply, h6₁]) (by simp [upd_apply, h6₂])
      (by simp [upd_apply, h18₁]) (by simp [upd_apply, h18₂]) (by simp [upd_apply, h4₁])
      (by simp [upd_apply, h4₂]) hrh₁ hrh₂ hb₁ hb₂ hm₁ hm₂
  · have e0 : BitVec.ofNat 64 w ≠ 0#64 := fun e => hw0 ((ofNat_eq_zero w (by omega)).mp e)
    rw [if_neg e0, pc4 pl.base 732 736]
    -- 736: add x5, x6, #0x48
    refine rs hc hr₁ hr₂ (f_30 hP hcl₁) (f_30 hP hcl₂)
      (ex_add_imm' 5#5 6#5 (by decide) (by decide) _ (BitVec.ofNat 64 L + 72#64)
        (by simp [upd_apply, h6₁] <;> rfl))
      (ex_add_imm' 5#5 6#5 (by decide) (by decide) _ (BitVec.ofNat 64 L + 72#64)
        (by simp [upd_apply, h6₂] <;> rfl)) rfl ?_
    rw [pc4 pl.base 736 740]
    -- 740: mov x3, #0
    refine rs hc hr₁ hr₂ (f_34 hP hcl₁) (f_34 hP hcl₂) (ex_movz64' 3#5 (by decide) _ 0#64 rfl)
      (ex_movz64' 3#5 (by decide) _ 0#64 rfl) rfl ?_
    rw [pc4 pl.base 740 744]
    -- 744: add x5, x0, x5
    have e5 : a + (BitVec.ofNat 64 L + 72#64) = a + 72#64 + BitVec.ofNat 64 L := by
      rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 L)]
    refine rs hc hr₁ hr₂ (f_38 hP hcl₁) (f_38 hP hcl₂)
      (ex_add_shift0' 5#5 0#5 5#5 (by decide) (by decide) (by decide) (a + 72#64 + BitVec.ofNat 64 L)
        (by simp only [upd_apply]; simp [h0₁]; exact e5))
      (ex_add_shift0' 5#5 0#5 5#5 (by decide) (by decide) (by decide) (a + 72#64 + BitVec.ofNat 64 L)
        (by simp only [upd_apply]; simp [h0₂]; exact e5)) rfl ?_
    rw [pc4 pl.base 744 748]
    -- 748: the loop
    generalize hW₁ : ((a + 64#64) ↦₆₄ BitVec.ofNat 64 L) ∗ (a ↦ₛ rh₁) ∗ ((a + 88#64) ↦ₛ [d₁.fin]) ∗
      ((a + 48#64) ↦ₛ d₁.pad) ∗ ((a + 89#64) ↦ₛ d₁.rest) ∗
      Cells4 T (c₁.regs.regs 29#5) (c₁.regs.regs 30#5) u2₁ u3₁ ∗ d₁.R = W₁
    generalize hW₂ : ((a + 64#64) ↦₆₄ BitVec.ofNat 64 L) ∗ (a ↦ₛ rh₂) ∗ ((a + 88#64) ↦ₛ [d₂.fin]) ∗
      ((a + 48#64) ↦ₛ d₂.pad) ∗ ((a + 89#64) ↦ₛ d₂.rest) ∗
      Cells4 T (c₂.regs.regs 29#5) (c₂.regs.regs 30#5) u2₂ u3₂ ∗ d₂.R = W₂
    have hm2₁ : m₁ ⊨ bytesIn d₁.ro p d₁.msg ∗ ((a + 72#64) ↦ₛ buf₁) ∗ W₁ :=
      Satisfies.of_eq hm₁ (by rw [← hW₁]; simp only [Mem, Fields]; ac_rfl)
    have hm2₂ : m₂ ⊨ bytesIn d₂.ro p d₂.msg ∗ ((a + 72#64) ↦ₛ buf₂) ∗ W₂ :=
      Satisfies.of_eq hm₂ (by rw [← hW₂]; simp only [Mem, Fields]; ac_rfl)
    have kq₁ := ((kk₁.upd 5#5 (by decide) (BitVec.ofNat 64 L + 72#64)).upd 3#5 (by decide) 0#64).upd
      5#5 (by decide) (a + 72#64 + BitVec.ofNat 64 L)
    have kq₂ := ((kk₂.upd 5#5 (by decide) (BitVec.ofNat 64 L + 72#64)).upd 3#5 (by decide) 0#64).upd
      5#5 (by decide) (a + 72#64 + BitVec.ofNat 64 L)
    refine copyLoop2 hc hr₁ hr₂ (pl.base + 748#64) T 18#5 2#5 5#5 1#5 3#5
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun m' h => f_3c hP h) (fun m' h => by rw [pc_add]; exact f_40 hP h)
      (fun m' h => by rw [pc_add]; exact f_44 hP h) (fun m' h => by rw [pc_add]; exact f_48 hP h)
      (fun m' h => by rw [pc_add]; exact f_4c hP h)
      p (a + 72#64) 0 L w (by omega) d₁.ro d₂.ro d₁.msg d₂.msg _ _ (by omega) (by omega)
      w (by omega) 0 _ _ _ _ m₁ m₂ buf₁ buf₂ (by omega) (by omega) (by omega) hcl₁ hcl₂
      (by simp [upd_apply, h18₁]) (by simp [upd_apply, h18₂]) (by simp [upd_apply])
      (by simp [upd_apply]) (by simp [upd_apply]) (by simp [upd_apply])
      (by simp [upd_apply]) (by simp [upd_apply]) hm2₁ hm2₂ ?_
    intro r₁' r₂' ps₁' ps₂' m₁' m₂' D₁' D₂' k₁ k₂ o₁ o₂ x₁ x₂ l₁ l₂ h₁ h₂
    rw [pcN pl.base 748 20 768]
    exact seg768 hc hP hr₁ hr₂ K784 K892 hTal k₁ k₂ (kq₁.frame o₁ (by decide) (by decide))
      (kq₂.frame o₂ (by decide) (by decide)) L n w hL0 hL16 hn64 hw.symm htgt hlen₁ hlen₂
      (by rw [o₁ 0#5 (by decide) (by decide)]; simp [upd_apply, h0₁])
      (by rw [o₂ 0#5 (by decide) (by decide)]; simp [upd_apply, h0₂])
      (by rw [o₁ 1#5 (by decide) (by decide)]; simp [upd_apply])
      (by rw [o₂ 1#5 (by decide) (by decide)]; simp [upd_apply])
      (by rw [o₁ 6#5 (by decide) (by decide)]; simp [upd_apply, h6₁])
      (by rw [o₂ 6#5 (by decide) (by decide)]; simp [upd_apply, h6₂])
      (by rw [o₁ 18#5 (by decide) (by decide)]; simp [upd_apply, h18₁])
      (by rw [o₂ 18#5 (by decide) (by decide)]; simp [upd_apply, h18₂])
      (by rw [o₁ 4#5 (by decide) (by decide)]; simp [upd_apply, h4₁])
      (by rw [o₂ 4#5 (by decide) (by decide)]; simp [upd_apply, h4₂])
      hrh₁ hrh₂ (l₁.trans hb₁) (l₂.trans hb₂)
      (Satisfies.of_eq h₁ (by rw [← hW₁]; simp only [Mem, Fields]; ac_rfl))
      (Satisfies.of_eq h₂ (by rw [← hW₂]; simp only [Mem, Fields]; ac_rfl))

end seg

end Poly1305DebianCtUpdate

end
end

section
section
/-! # `poly1305_update` in both runs: the relational lemma `update_rel`

The prologue (688–712) signs the return address (`paciasp`, a hint), saves `x29, x30` in a 32-byte
frame, keeps the message pointer in `x18` and its length in `x4`, loads `leftover` (public) and
branches on it: to "handle leftover" (`seg716`) when it is nonzero, else to the whole-block path
(`seg828`). Every path ends in one of the two epilogues (784, 892) (`exit2`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtUpdate

open Arm64 Arm64.Obj Poly1305DebianCt Leakage Poly1305DebianCtFw Poly1305Boringssl
open Poly1305Libsodium (u64At bytesIn)

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

theorem ex_ldp64_post_sp' (a b : BitVec 5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (off : BitVec 64)
    (hal : (sp &&& 0b1111#64) = 0#64) (hr1 : m.canRead sp 8 = true)
    (hr2 : m.canRead (sp + 8#64) 8 = true) (va vb : BitVec 64) (hva : m.read64 sp = va)
    (hvb : m.read64 (sp + 8#64) = vb) :
    execInstWithSvc svc (.ldp .W64 false (.gpr a) (.gpr b) (.PostIndex .sp off))
        (mkS s0 pc r sp ps m v) =
      mkS s0 (pc + 4#64) (upd (upd r a va) b vb) (sp + off) ps m v := by
  rw [ex_ldp64_post_sp a b ha hb off hal hr1 hr2, hva, hvb]

end exec

section top

variable {pl : Placement} {X : String → Option (State → State)} {stop₁ stop₂ : State → Prop}

set_option maxHeartbeats 4000000 in
/-- The epilogue `ldp x29, x30, [sp], #32; autiasp; ret` at `pcE` in both runs: they return to
their own `x30` with `sp` back at entry, `x19..x30` as at entry, and the state bytes reassembled. -/
theorem exit2 (hc : StopCompat stop₁ stop₂) {c₁ c₂ : State}
    (hr₁ : c₁.status = .Running) (hr₂ : c₂.status = .Running) {pcE : BitVec 64}
    (hf1 : ∀ m', (P pl X).CodeLoaded m' → (P pl X).fetchMem m' pcE =
      some (.ldp .W64 false (.gpr 0x1d#5) (.gpr 0x1e#5) (.PostIndex .sp 0x0000000000000020#64)))
    (hf2 : ∀ m', (P pl X).CodeLoaded m' → (P pl X).fetchMem m' (pcE + 4#64) = some (.hint 0x1d#7))
    (hf3 : ∀ m', (P pl X).CodeLoaded m' → (P pl X).fetchMem m' (pcE + 4#64 + 4#64) =
      some (.ret (.gpr 0x1e#5)))
    {d₁ d₂ : RunD} {a p : BitVec 64} {tgt : Nat} (hal : c₁.sp &&& 0b1111#64 = 0#64)
    (hpad₁ : d₁.pad.length = 16) (hpad₂ : d₂.pad.length = 16)
    (hrest₁ : d₁.rest.length = 7) (hrest₂ : d₂.rest.length = 7)
    (Kf : ∀ (r₁ r₂ : BitVec 5 → BitVec 64) (ps₁ ps₂ : PState) (m₁ m₂ : Memory)
      (st₁ st₂ : List (BitVec 8)),
      (∀ k : BitVec 5, 19 ≤ k.toNat → r₁ k = c₁.regs.regs k) →
      (∀ k : BitVec 5, 19 ≤ k.toNat → r₂ k = c₂.regs.regs k) →
      st₁.length = 96 → st₂.length = 96 → u64At st₁ 64 = tgt → u64At st₂ 64 = tgt →
      (m₁ ⊨ ((a ↦ₛ st₁) ∗ bytesIn d₁.ro p d₁.msg ∗ memRegion (c₁.sp - 32#64) 32) ∗ d₁.R) →
      (m₂ ⊨ ((a ↦ₛ st₂) ∗ bytesIn d₂.ro p d₂.msg ∗ memRegion (c₁.sp - 32#64) 32) ∗ d₂.R) →
      ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ (c₁.regs.regs 30#5) r₁ c₁.sp ps₁ m₁ c₁.vregs.regs)
        (mkS c₂ (c₂.regs.regs 30#5) r₂ c₁.sp ps₂ m₂ c₂.vregs.regs)) :
    ExitK2 pl X stop₁ stop₂ c₁ c₂ d₁ d₂ pcE a p (c₁.sp - 32#64) tgt := by
  intro r₁ r₂ ps₁ ps₂ m₁ m₂ rh₁ rh₂ buf₁ buf₂ lo u2₁ u3₁ u2₂ u3₂ k₁ k₂ kp₁ kp₂ lr₁ lr₂ lb₁ lb₂ hlo
    hm₁ hm₂
  have hTal : (c₁.sp - 32#64) &&& 0b1111#64 = 0#64 := al16_sub _ 32 (by norm_num) (by norm_num) hal
  generalize hT : c₁.sp - 32#64 = T at hTal hm₁ hm₂ ⊢
  generalize hG₁ : Fields a rh₁ d₁.pad lo buf₁ d₁.fin d₁.rest ∗ bytesIn d₁.ro p d₁.msg = G₁
  generalize hG₂ : Fields a rh₂ d₂.pad lo buf₂ d₂.fin d₂.rest ∗ bytesIn d₂.ro p d₂.msg = G₂
  have hm0₁ : m₁ ⊨ (T ↦₆₄ c₁.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ c₁.regs.regs 30#5) ∗
      ((T + 0x10#64) ↦₆₄ u2₁) ∗ ((T + 0x10#64 + 8#64) ↦₆₄ u3₁) ∗ (G₁ ∗ d₁.R) :=
    Satisfies.of_eq hm₁ (by rw [← hG₁]; simp only [Mem, Cells4]; ac_rfl)
  have hm0₂ : m₂ ⊨ (T ↦₆₄ c₂.regs.regs 29#5) ∗ ((T + 8#64) ↦₆₄ c₂.regs.regs 30#5) ∗
      ((T + 0x10#64) ↦₆₄ u2₂) ∗ ((T + 0x10#64 + 8#64) ↦₆₄ u3₂) ∗ (G₂ ∗ d₂.R) :=
    Satisfies.of_eq hm₂ (by rw [← hG₂]; simp only [Mem, Cells4]; ac_rfl)
  have e0₁ := sat64_read hm0₁
  have e0₂ := sat64_read hm0₂
  have e1₁ := sat64_read (Satisfies.of_eq hm0₁ (Q := ((T + 8#64) ↦₆₄ c₁.regs.regs 30#5) ∗
    ((T ↦₆₄ c₁.regs.regs 29#5) ∗ ((T + 0x10#64) ↦₆₄ u2₁) ∗ ((T + 0x10#64 + 8#64) ↦₆₄ u3₁) ∗
      (G₁ ∗ d₁.R))))
  have e1₂ := sat64_read (Satisfies.of_eq hm0₂ (Q := ((T + 8#64) ↦₆₄ c₂.regs.regs 30#5) ∗
    ((T ↦₆₄ c₂.regs.regs 29#5) ∗ ((T + 0x10#64) ↦₆₄ u2₂) ∗ ((T + 0x10#64 + 8#64) ↦₆₄ u3₂) ∗
      (G₂ ∗ d₂.R))))
  -- ldp x29, x30, [sp], #32
  refine rs hc hr₁ hr₂ (hf1 m₁ k₁) (hf1 m₂ k₂)
    (ex_ldp64_post_sp' 29#5 30#5 (by decide) (by decide) _ hTal e0₁.2.1 e1₁.2.1 _ _ e0₁.1 e1₁.1)
    (ex_ldp64_post_sp' 29#5 30#5 (by decide) (by decide) _ hTal e0₂.2.1 e1₂.2.1 _ _ e0₂.1 e1₂.1)
    (by simp [leakedValues, evalAddrMode]) ?_
  -- autiasp
  refine rs hc hr₁ hr₂ (hf2 m₁ k₁) (hf2 m₂ k₂) (ex_hint _) (ex_hint _) rfl ?_
  -- ret
  refine rs hc hr₁ hr₂ (hf3 m₁ k₁) (hf3 m₂ k₂) ex_ret ex_ret rfl ?_
  have hS : T + 0x0000000000000020#64 = c₁.sp := by rw [← hT]; bv_omega
  rw [upd_same, upd_same, hS]
  have kept : ∀ (r : BitVec 5 → BitVec 64) (c : State), Kept r c.regs.regs →
      ∀ k : BitVec 5, 19 ≤ k.toNat →
        upd (upd r 29#5 (c.regs.regs 29#5)) 30#5 (c.regs.regs 30#5) k = c.regs.regs k := by
    intro r c hk k h1
    by_cases h30 : k = 30#5
    · subst h30; simp
    by_cases h29 : k = 29#5
    · subst h29; simp [upd_apply]
    rw [upd_ne _ _ h30, upd_ne _ _ h29]
    exact hk k h1 (fun e => h29 (BitVec.eq_of_toNat_eq (by simpa using e)))
      (fun e => h30 (BitVec.eq_of_toNat_eq (by simpa using e)))
  refine Kf _ _ _ _ m₁ m₂ (rh₁ ++ d₁.pad ++ unpack64 lo ++ buf₁ ++ d₁.fin :: d₁.rest)
    (rh₂ ++ d₂.pad ++ unpack64 lo ++ buf₂ ++ d₂.fin :: d₂.rest) (kept r₁ c₁ kp₁) (kept r₂ c₂ kp₂)
    (by simp [lr₁, hpad₁, lb₁, hrest₁]) (by simp [lr₂, hpad₂, lb₂, hrest₂])
    (by rw [u64At_fields _ _ _ _ _ _ lr₁ hpad₁ (unpack64_length lo), leBytesToNum_unpack64, hlo])
    (by rw [u64At_fields _ _ _ _ _ _ lr₂ hpad₂ (unpack64_length lo), leBytesToNum_unpack64, hlo])
    ?_ ?_
  · rw [fields_eq a rh₁ d₁.pad buf₁ d₁.rest lo d₁.fin lr₁ hpad₁ lb₁]
    have h1 := Satisfies.of_eq hm₁ (Q := Cells4 T (c₁.regs.regs 29#5) (c₁.regs.regs 30#5) u2₁ u3₁ ∗
      (Fields a rh₁ d₁.pad lo buf₁ d₁.fin d₁.rest ∗ bytesIn d₁.ro p d₁.msg ∗ d₁.R)) (by
        simp only [Mem]; ac_rfl)
    have h2 := sat_sep_mono h1 (region_of_cells4 T _ _ u2₁ u3₁)
    rw [hT]
    exact Satisfies.of_eq h2
  · rw [fields_eq a rh₂ d₂.pad buf₂ d₂.rest lo d₂.fin lr₂ hpad₂ lb₂]
    have h1 := Satisfies.of_eq hm₂ (Q := Cells4 T (c₂.regs.regs 29#5) (c₂.regs.regs 30#5) u2₂ u3₂ ∗
      (Fields a rh₂ d₂.pad lo buf₂ d₂.fin d₂.rest ∗ bytesIn d₂.ro p d₂.msg ∗ d₂.R)) (by
        simp only [Mem]; ac_rfl)
    have h2 := sat_sep_mono h1 (region_of_cells4 T _ _ u2₂ u3₂)
    rw [hT]
    exact Satisfies.of_eq h2

end top

end Poly1305DebianCtUpdate

end
end

section
section
/-! # `update_rel`: `poly1305_update` in both runs, in continuation-passing form

Entry: both runs at `poly1305_update` (text offset 688), running, code loaded, `sp` aligned and
equal, equal `x0` (state), `x1` (message), `x2` (length), each memory satisfying
`updateIntPre pl (ro, st, msg) c ∗ F`, with the same stored `leftover` (`u64At st 64`).
Exit: both runs back at their `lr` with `sp` restored, `x19..x30` (and the vector registers) as at
entry, and memory satisfying `updateIntPre pl (ro, st', msg) c ∗ F` for new state bytes `st'` whose
`leftover` is `(leftover + length) % 16`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtUpdate

open Arm64 Arm64.Obj Poly1305DebianCt Leakage Poly1305DebianCtFw Poly1305Boringssl
open Poly1305Libsodium (u64At bytesIn)

set_option maxHeartbeats 4000000 in
theorem Kept.refl (r : BitVec 5 → BitVec 64) : Kept r r := fun _ _ _ _ => rfl

/-- What `updateIntPre` gives about a run's entry memory: the state as fields, the frame as cells. -/
theorem entry_mem {pl : Placement} {c : State} {F : SepProp} {ro : Bool}
    {st msg : List (BitVec 8)} (h : c.mem ⊨ updateIntPre pl (ro, st, msg) c ∗ F) :
    u64At st 64 < 16 ∧ (c.readReg64 Reg.x2).toNat = msg.length ∧
    ∃ (rh pad w0 buf : List (BitVec 8)) (fin : BitVec 8) (rest : List (BitVec 8))
      (u0 u1 u2 u3 : BitVec 64),
      rh.length = 48 ∧ pad.length = 16 ∧ buf.length = 16 ∧ rest.length = 7 ∧
      u64At st 64 = (pack64 w0).toNat ∧
      (c.mem ⊨ Fields (c.readReg64 Reg.x0) rh pad (pack64 w0) buf fin rest ∗
        bytesIn ro (c.readReg64 Reg.x1) msg ∗ Cells4 (c.sp - 32#64) u0 u1 u2 u3 ∗ F) := by
  simp only [updateIntPre] at h
  rw [sepConj_assoc, sat_pure_sep] at h
  obtain ⟨⟨hlen, hL16, hn⟩, h⟩ := h
  refine ⟨hL16, hn, ?_⟩
  have hsplit := split96 st hlen
  have l1 : (st.take 48).length = 48 := by simp; omega
  have l2 : ((st.drop 48).take 16).length = 16 := by simp; omega
  have l3 : ((st.drop 64).take 8).length = 8 := by simp; omega
  have l4 : ((st.drop 72).take 16).length = 16 := by simp; omega
  have l5 : (st.drop 89).length = 7 := by simp; omega
  generalize st.take 48 = rh0 at hsplit l1
  generalize (st.drop 48).take 16 = pad at hsplit l2
  generalize (st.drop 64).take 8 = w0 at hsplit l3
  generalize (st.drop 72).take 16 = buf0 at hsplit l4
  generalize st.getD 88 0#8 = fin at hsplit
  generalize st.drop 89 = rest at hsplit l5
  subst hsplit
  have hLw : u64At (rh0 ++ pad ++ w0 ++ buf0 ++ fin :: rest) 64 = (pack64 w0).toNat := by
    rw [u64At_fields _ _ _ _ _ _ l1 l2 l3, toNat_pack64 w0 l3]
  have hfe : (c.readReg64 Reg.x0 ↦ₛ (rh0 ++ pad ++ w0 ++ buf0 ++ fin :: rest)) =
      Fields (c.readReg64 Reg.x0) rh0 pad (pack64 w0) buf0 fin rest := by
    rw [← fields_eq _ rh0 pad buf0 rest (pack64 w0) fin l1 l2 l4, unpack64_pack64 w0 l3]
  rw [hfe] at h
  have h1 := Satisfies.of_eq h (Q := memRegion (c.sp - 32#64) 32 ∗
    (Fields (c.readReg64 Reg.x0) rh0 pad (pack64 w0) buf0 fin rest ∗
      bytesIn ro (c.readReg64 Reg.x1) msg ∗ F))
  obtain ⟨u0, u1, u2, u3, h2⟩ := cells4_of_region h1
  exact ⟨rh0, pad, w0, buf0, fin, rest, u0, u1, u2, u3, l1, l2, l4, l5, hLw,
    Satisfies.of_eq h2⟩

set_option maxHeartbeats 8000000 in
/-- `poly1305_update` in both runs (see the module docstring). -/
theorem update_rel {pl : Placement} {X : String → Option (State → State)}
    {stop₁ stop₂ : State → Prop} (hc : StopCompat stop₁ stop₂)
    (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl) {c₁ c₂ : State}
    (hrun₁ : c₁.status = .Running) (hrun₂ : c₂.status = .Running)
    (hpc₁ : c₁.pc = pl.base + 688#64) (hpc₂ : c₂.pc = pl.base + 688#64)
    (hcl₁ : (P pl X).CodeLoaded c₁.mem) (hcl₂ : (P pl X).CodeLoaded c₂.mem)
    (hal : c₁.spAligned = true) (hsp : c₁.sp = c₂.sp)
    (hx0 : c₁.readReg64 Reg.x0 = c₂.readReg64 Reg.x0)
    (hx1 : c₁.readReg64 Reg.x1 = c₂.readReg64 Reg.x1)
    (hx2 : c₁.readReg64 Reg.x2 = c₂.readReg64 Reg.x2)
    {F₁ F₂ : SepProp} {ro₁ ro₂ : Bool} {st₁ st₂ msg₁ msg₂ : List (BitVec 8)}
    (hpre₁ : c₁.mem ⊨ updateIntPre pl (ro₁, st₁, msg₁) c₁ ∗ F₁)
    (hpre₂ : c₂.mem ⊨ updateIntPre pl (ro₂, st₂, msg₂) c₂ ∗ F₂)
    (hlo : u64At st₁ 64 = u64At st₂ 64)
    (K : ∀ (r₁ r₂ : BitVec 5 → BitVec 64) (ps₁ ps₂ : PState) (m₁ m₂ : Memory)
      (st₁' st₂' : List (BitVec 8)),
      (∀ k : BitVec 5, 19 ≤ k.toNat → r₁ k = c₁.regs.regs k) →
      (∀ k : BitVec 5, 19 ≤ k.toNat → r₂ k = c₂.regs.regs k) →
      u64At st₁' 64 = (u64At st₁ 64 + msg₁.length) % 16 →
      u64At st₂' 64 = (u64At st₂ 64 + msg₂.length) % 16 →
      (m₁ ⊨ updateIntPre pl (ro₁, st₁', msg₁) c₁ ∗ F₁) →
      (m₂ ⊨ updateIntPre pl (ro₂, st₂', msg₂) c₂ ∗ F₂) →
      ObsEquiv (P pl X) arity stop₁ stop₂
        (mkS c₁ (c₁.readReg64 Reg.lr) r₁ c₁.sp ps₁ m₁ c₁.vregs.regs)
        (mkS c₂ (c₂.readReg64 Reg.lr) r₂ c₂.sp ps₂ m₂ c₂.vregs.regs)) :
    ObsEquiv (P pl X) arity stop₁ stop₂ c₁ c₂ := by
  obtain ⟨hL₁, hn₁, rh₁, pad₁, w₁, buf₁, fin₁, rest₁, u0₁, u1₁, u2₁, u3₁, l1₁, l2₁, l4₁, l5₁, hw₁,
    hm₁⟩ := entry_mem hpre₁
  obtain ⟨hL₂, hn₂, rh₂, pad₂, w₂, buf₂, fin₂, rest₂, u0₂, u1₂, u2₂, u3₂, l1₂, l2₂, l4₂, l5₂, hw₂,
    hm₂⟩ := entry_mem hpre₂
  have hn : msg₂.length = msg₁.length := by rw [← hn₁, ← hn₂, hx2]
  have hn64 : msg₁.length < 2 ^ 64 := by rw [← hn₁]; exact BitVec.isLt _
  have hlo' : pack64 w₂ = pack64 w₁ := BitVec.eq_of_toNat_eq (by rw [← hw₁, ← hw₂, hlo])
  rw [hlo', ← hx0, ← hx1, ← hsp] at hm₂
  generalize hlo1 : pack64 w₁ = lo at hm₁ hm₂ hw₁
  generalize ha : c₁.readReg64 Reg.x0 = a at hm₁ hm₂
  generalize hp : c₁.readReg64 Reg.x1 = p at hm₁ hm₂
  have hal0 : c₁.sp &&& 0b1111#64 = 0#64 := by simpa [State.spAligned] using hal
  have hTal : (c₁.sp - 32#64) &&& 0b1111#64 = 0#64 := al16_sub _ 32 (by norm_num) (by norm_num) hal0
  -- the registers at entry
  have r0₁ : c₁.regs.regs 0#5 = a := by rw [← ha, readGpr_eq c₁ 0#5 (by decide)]
  have r0₂ : c₂.regs.regs 0#5 = a := by rw [← ha, hx0, readGpr_eq c₂ 0#5 (by decide)]
  have r1₁ : c₁.regs.regs 1#5 = p := by rw [← hp, readGpr_eq c₁ 1#5 (by decide)]
  have r1₂ : c₂.regs.regs 1#5 = p := by rw [← hp, hx1, readGpr_eq c₂ 1#5 (by decide)]
  have r2₁ : c₁.regs.regs 2#5 = BitVec.ofNat 64 msg₁.length := by
    rw [← readGpr_eq c₁ 2#5 (by decide)]
    exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]; exact hn₁)
  have r2₂ : c₂.regs.regs 2#5 = BitVec.ofNat 64 msg₁.length := by
    rw [← readGpr_eq c₂ 2#5 (by decide), ← hx2]
    exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]; exact hn₁)
  -- each run's data
  let d₁ : RunD := ⟨ro₁, msg₁, pad₁, rest₁, fin₁, F₁⟩
  let d₂ : RunD := ⟨ro₂, msg₂, pad₂, rest₂, fin₂, F₂⟩
  set tgt := (u64At st₁ 64 + msg₁.length) % 16 with htgt
  -- the exits
  have Kf : ∀ (r₁ r₂ : BitVec 5 → BitVec 64) (ps₁ ps₂ : PState) (m₁ m₂ : Memory)
      (s₁ s₂ : List (BitVec 8)),
      (∀ k : BitVec 5, 19 ≤ k.toNat → r₁ k = c₁.regs.regs k) →
      (∀ k : BitVec 5, 19 ≤ k.toNat → r₂ k = c₂.regs.regs k) →
      s₁.length = 96 → s₂.length = 96 → u64At s₁ 64 = tgt → u64At s₂ 64 = tgt →
      (m₁ ⊨ ((a ↦ₛ s₁) ∗ bytesIn d₁.ro p d₁.msg ∗ memRegion (c₁.sp - 32#64) 32) ∗ d₁.R) →
      (m₂ ⊨ ((a ↦ₛ s₂) ∗ bytesIn d₂.ro p d₂.msg ∗ memRegion (c₁.sp - 32#64) 32) ∗ d₂.R) →
      ObsEquiv (P pl X) arity stop₁ stop₂ (mkS c₁ (c₁.regs.regs 30#5) r₁ c₁.sp ps₁ m₁ c₁.vregs.regs)
        (mkS c₂ (c₂.regs.regs 30#5) r₂ c₁.sp ps₂ m₂ c₂.vregs.regs) := by
    intro r₁ r₂ ps₁ ps₂ m₁ m₂ s₁ s₂ k₁ k₂ ls₁ ls₂ u₁ u₂ h₁ h₂
    refine oe_congr (t₁ := mkS c₁ (c₁.readReg64 Reg.lr) r₁ c₁.sp ps₁ m₁ c₁.vregs.regs)
      (t₂ := mkS c₂ (c₂.readReg64 Reg.lr) r₂ c₂.sp ps₂ m₂ c₂.vregs.regs)
      (by rw [show c₁.readReg64 Reg.lr = c₁.regs.regs 30#5 from readGpr_eq c₁ 30#5 (by decide)])
      (by rw [show c₂.readReg64 Reg.lr = c₂.regs.regs 30#5 from readGpr_eq c₂ 30#5 (by decide),
        hsp]) ?_
    refine K r₁ r₂ ps₁ ps₂ m₁ m₂ s₁ s₂ k₁ k₂ u₁ (by rw [u₂, htgt, hlo, hn]) ?_ ?_
    · simp only [updateIntPre]
      rw [sepConj_assoc, sat_pure_sep]
      refine ⟨⟨ls₁, by omega, hn₁⟩, ?_⟩
      rw [ha, hp]
      exact h₁
    · simp only [updateIntPre]
      rw [sepConj_assoc, sat_pure_sep]
      refine ⟨⟨ls₂, by omega, hn₂⟩, ?_⟩
      have hsf : stackFrame c₂ 32 = memRegion (c₁.sp - 32#64) 32 := by rw [hsp]
      rw [← hx0, ha, ← hx1, hp, hsf]
      exact h₂
  have K784 := exit2 (pl := pl) (X := X) hc hrun₁ hrun₂ (pcE := pl.base + 784#64)
    (fun m' h => f_60 hP h) (fun m' h => by rw [pc4 pl.base 784 788]; exact f_64 hP h)
    (fun m' h => by rw [pc4 pl.base 784 788, pc4 pl.base 788 792]; exact f_68 hP h)
    (d₁ := d₁) (d₂ := d₂) (a := a) (p := p) hal0 l2₁ l2₂ l5₁ l5₂ Kf
  have K892 := exit2 (pl := pl) (X := X) hc hrun₁ hrun₂ (pcE := pl.base + 892#64)
    (fun m' h => f_cc hP h) (fun m' h => by rw [pc4 pl.base 892 896]; exact f_d0 hP h)
    (fun m' h => by rw [pc4 pl.base 892 896, pc4 pl.base 896 900]; exact f_d4 hP h)
    (d₁ := d₁) (d₂ := d₂) (a := a) (p := p) hal0 l2₁ l2₂ l5₁ l5₂ Kf
  -- the run
  refine oe_congr (t₁ := mkS c₁ (pl.base + 688#64) c₁.regs.regs c₁.sp c₁.pstate c₁.mem c₁.vregs.regs)
    (t₂ := mkS c₂ (pl.base + 688#64) c₂.regs.regs c₁.sp c₂.pstate c₂.mem c₂.vregs.regs)
    (by rw [← hpc₁]; rfl) (by rw [hsp, ← hpc₂]; rfl) ?_
  -- 688: paciasp
  refine rs hc hrun₁ hrun₂ (f_0 hP hcl₁) (f_0 hP hcl₂) (ex_hint _) (ex_hint _) rfl ?_
  rw [pc4 pl.base 688 692]
  -- 692: stp x29, x30, [sp, #-32]!
  have eT : c₁.sp + 0xffffffffffffffe0#64 = c₁.sp - 32#64 := by bv_omega
  replace hm₁ := Satisfies.of_eq hm₁ (Q := Cells4 (c₁.sp - 32#64) u0₁ u1₁ u2₁ u3₁ ∗
    (Fields a rh₁ pad₁ lo buf₁ fin₁ rest₁ ∗ bytesIn ro₁ p msg₁ ∗ F₁))
  replace hm₂ := Satisfies.of_eq hm₂ (Q := Cells4 (c₁.sp - 32#64) u0₂ u1₂ u2₂ u3₂ ∗
    (Fields a rh₂ pad₂ lo buf₂ fin₂ rest₂ ∗ bytesIn ro₂ p msg₂ ∗ F₂))
  generalize hG₁ : Fields a rh₁ pad₁ lo buf₁ fin₁ rest₁ ∗ bytesIn ro₁ p msg₁ ∗ F₁ = G₁ at hm₁
  generalize hG₂ : Fields a rh₂ pad₂ lo buf₂ fin₂ rest₂ ∗ bytesIn ro₂ p msg₂ ∗ F₂ = G₂ at hm₂
  simp only [Cells4, sepConj_assoc] at hm₁ hm₂
  have q0₁ := sat64_read hm₁
  have q0₂ := sat64_read hm₂
  have hm₁' := Satisfies.of_eq hm₁ (Q := ((c₁.sp - 32#64 + 8#64) ↦₆₄ u1₁) ∗ ((c₁.sp - 32#64) ↦₆₄ u0₁) ∗
    ((c₁.sp - 32#64 + 0x10#64) ↦₆₄ u2₁) ∗ ((c₁.sp - 32#64 + 0x10#64 + 8#64) ↦₆₄ u3₁) ∗ G₁)
  have hm₂' := Satisfies.of_eq hm₂ (Q := ((c₁.sp - 32#64 + 8#64) ↦₆₄ u1₂) ∗ ((c₁.sp - 32#64) ↦₆₄ u0₂) ∗
    ((c₁.sp - 32#64 + 0x10#64) ↦₆₄ u2₂) ∗ ((c₁.sp - 32#64 + 0x10#64 + 8#64) ↦₆₄ u3₂) ∗ G₂)
  have q1₁ := sat64_read hm₁'
  have q1₂ := sat64_read hm₂'
  refine rsw hc hrun₁ hrun₂ hcl₁ hcl₂ (f_4 hP hcl₁) (f_4 hP hcl₂)
    (ex_stp64_pre_sp 29#5 30#5 (by decide) (by decide) _ hal0 (by rw [eT]; exact q0₁.2.2)
      (by rw [eT]; exact q1₁.2.2))
    (ex_stp64_pre_sp 29#5 30#5 (by decide) (by decide) _ hal0 (by rw [eT]; exact q0₂.2.2)
      (by rw [eT]; exact q1₂.2.2))
    (by simp [leakedValues, evalAddrMode]) ?_
  intro k₁ k₂
  rw [eT, pc4 pl.base 692 696]
  rw [eT] at k₁ k₂
  have w1₁ := sat64_write (Satisfies.of_eq (sat64_write hm₁ (c₁.regs.regs 29#5))
    (Q := ((c₁.sp - 32#64 + 8#64) ↦₆₄ u1₁) ∗ ((c₁.sp - 32#64) ↦₆₄ c₁.regs.regs 29#5) ∗
    ((c₁.sp - 32#64 + 0x10#64) ↦₆₄ u2₁) ∗ ((c₁.sp - 32#64 + 0x10#64 + 8#64) ↦₆₄ u3₁) ∗ G₁))
    (c₁.regs.regs 30#5)
  have w1₂ := sat64_write (Satisfies.of_eq (sat64_write hm₂ (c₂.regs.regs 29#5))
    (Q := ((c₁.sp - 32#64 + 8#64) ↦₆₄ u1₂) ∗ ((c₁.sp - 32#64) ↦₆₄ c₂.regs.regs 29#5) ∗
    ((c₁.sp - 32#64 + 0x10#64) ↦₆₄ u2₂) ∗ ((c₁.sp - 32#64 + 0x10#64 + 8#64) ↦₆₄ u3₂) ∗ G₂))
    (c₂.regs.regs 30#5)
  generalize (c₁.mem.write64 (c₁.sp - 32#64) (c₁.regs.regs 29#5)).write64 (c₁.sp - 32#64 + 8#64)
    (c₁.regs.regs 30#5) = n₁ at w1₁ k₁ ⊢
  generalize (c₂.mem.write64 (c₁.sp - 32#64) (c₂.regs.regs 29#5)).write64 (c₁.sp - 32#64 + 8#64)
    (c₂.regs.regs 30#5) = n₂ at w1₂ k₂ ⊢
  simp only [mkS_mem] at k₁ k₂
  -- 696: mov x18, x1
  refine rs hc hrun₁ hrun₂ (f_8 hP k₁) (f_8 hP k₂) (ex_mov' 18#5 1#5 (by decide) (by decide) p r1₁)
    (ex_mov' 18#5 1#5 (by decide) (by decide) p r1₂) rfl ?_
  rw [pc4 pl.base 696 700]
  -- 700: mov x4, x2
  refine rs hc hrun₁ hrun₂ (f_c hP k₁) (f_c hP k₂)
    (ex_mov' 4#5 2#5 (by decide) (by decide) _ (by rw [upd_ne _ _ (by decide), r2₁]))
    (ex_mov' 4#5 2#5 (by decide) (by decide) _ (by rw [upd_ne _ _ (by decide), r2₂])) rfl ?_
  rw [pc4 pl.base 700 704]
  -- 704: mov x29, sp
  refine rs hc hrun₁ hrun₂ (f_10 hP k₁) (f_10 hP k₂) (ex_add_gpr_sp 29#5 (by decide) _)
    (ex_add_gpr_sp 29#5 (by decide) _) rfl ?_
  rw [pc4 pl.base 704 708]
  -- 708: ldr x6, [x0, #0x40]
  rw [← hG₁] at w1₁
  rw [← hG₂] at w1₂
  have hw1₁ : n₁ ⊨ ((a + 64#64) ↦₆₄ lo) ∗ (((a + 72#64) ↦ₛ buf₁) ∗ (a ↦ₛ rh₁) ∗
      ((a + 88#64) ↦ₛ [fin₁]) ∗ ((a + 48#64) ↦ₛ pad₁) ∗ ((a + 89#64) ↦ₛ rest₁) ∗
      bytesIn ro₁ p msg₁ ∗
      Cells4 (c₁.sp - 32#64) (c₁.regs.regs 29#5) (c₁.regs.regs 30#5) u2₁ u3₁ ∗ F₁) :=
    Satisfies.of_eq w1₁ (by simp only [Fields, Cells4]; ac_rfl)
  have hw1₂ : n₂ ⊨ ((a + 64#64) ↦₆₄ lo) ∗ (((a + 72#64) ↦ₛ buf₂) ∗ (a ↦ₛ rh₂) ∗
      ((a + 88#64) ↦ₛ [fin₂]) ∗ ((a + 48#64) ↦ₛ pad₂) ∗ ((a + 89#64) ↦ₛ rest₂) ∗
      bytesIn ro₂ p msg₂ ∗
      Cells4 (c₁.sp - 32#64) (c₂.regs.regs 29#5) (c₂.regs.regs 30#5) u2₂ u3₂ ∗ F₂) :=
    Satisfies.of_eq w1₂ (by simp only [Fields, Cells4]; ac_rfl)
  have c2₁ := sat64_read hw1₁
  have c2₂ := sat64_read hw1₂
  refine rs hc hrun₁ hrun₂ (f_14 hP k₁) (f_14 hP k₂)
    (ex_ldr64_gpr' 6#5 0#5 (by decide) (by decide) _ _ (by simp [upd_apply, r0₁]) c2₁.2.1)
    (ex_ldr64_gpr' 6#5 0#5 (by decide) (by decide) _ _ (by simp [upd_apply, r0₂]) c2₂.2.1)
    (by simp [leakedValues, evalAddrMode, upd_apply, r0₁, r0₂]) ?_
  rw [c2₁.1, c2₂.1, pc4 pl.base 708 712]
  have hm6₁ : n₁ ⊨ Mem c₁ d₁ a p (c₁.sp - 32#64) lo rh₁ buf₁ u2₁ u3₁ :=
    Satisfies.of_eq hw1₁ (by simp only [Mem, Fields]; ac_rfl)
  have hm6₂ : n₂ ⊨ Mem c₂ d₂ a p (c₁.sp - 32#64) lo rh₂ buf₂ u2₂ u3₂ :=
    Satisfies.of_eq hw1₂ (by simp only [Mem, Fields]; ac_rfl)
  have kk₁ : Kept (upd (upd (upd (upd c₁.regs.regs 18#5 p) 4#5 (BitVec.ofNat 64 msg₁.length)) 29#5
      (c₁.sp - 32#64 + BitVec.zeroExtend 64 0x000#12)) 6#5 lo) c₁.regs.regs :=
    ((((Kept.refl c₁.regs.regs).upd 18#5 (by decide) _).upd 4#5
      (by decide) _).upd 29#5 (by decide) _).upd 6#5 (by decide) _
  have kk₂ : Kept (upd (upd (upd (upd c₂.regs.regs 18#5 p) 4#5 (BitVec.ofNat 64 msg₁.length)) 29#5
      (c₁.sp - 32#64 + BitVec.zeroExtend 64 0x000#12)) 6#5 lo) c₂.regs.regs :=
    ((((Kept.refl c₂.regs.regs).upd 18#5 (by decide) _).upd 4#5
      (by decide) _).upd 29#5 (by decide) _).upd 6#5 (by decide) _
  -- 712: cbz x6, 828
  refine rs hc hrun₁ hrun₂ (f_18 hP k₁) (f_18 hP k₂) (ex_cbz 6#5 (by decide) _)
    (ex_cbz 6#5 (by decide) _) rfl ?_
  rw [upd_same, upd_same]
  have hLlo : lo.toNat < 16 := by rw [← hw₁]; exact hL₁
  by_cases hL0 : lo = 0#64
  · rw [if_pos hL0, show pl.base + 712#64 + 0x0000000000000074#64 = pl.base + 828#64 by bv_omega]
    rw [hL0] at hm6₁ hm6₂
    exact seg828 hc hP hrun₁ hrun₂ K784 K892 hTal k₁ k₂ kk₁ kk₂ 0 msg₁.length
      (by rw [htgt, hw₁, hL0]; simp) (by omega) (Nat.zero_add _).symm
      (by show msg₂.length = 0 + msg₁.length; omega)
      (by simp [upd_apply, r0₁]) (by simp [upd_apply, r0₂]) (by simp [upd_apply])
      (by simp [upd_apply]) (by simp [upd_apply]) (by simp [upd_apply]) l1₁ l1₂ l4₁ l4₂ hm6₁ hm6₂
  · rw [if_neg hL0, pc4 pl.base 712 716]
    have elo : lo = BitVec.ofNat 64 lo.toNat := by simp
    have hLpos : 0 < lo.toNat := by
      rcases Nat.eq_zero_or_pos lo.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hL0
      · exact h
    rw [elo] at hm6₁ hm6₂
    exact seg716 hc hP hrun₁ hrun₂ K784 K892 hTal k₁ k₂ kk₁ kk₂ lo.toNat msg₁.length hLpos hLlo hn64
      (by rw [htgt, hw₁]) rfl hn
      (by simp [upd_apply, r0₁]) (by simp [upd_apply, r0₂]) (by simp [upd_apply, r2₁])
      (by simp [upd_apply, r2₂]) (by simp [upd_apply]) (by simp [upd_apply])
      (by simp [upd_apply]) (by simp [upd_apply]) (by simp [upd_apply]) (by simp [upd_apply])
      l1₁ l1₂ l4₁ l4₂ hm6₁ hm6₂

end Poly1305DebianCtUpdate

end
end

section
section
/-! # `poly1305_update` is constant-time (`ctInternalOk`)

Two entry states that differ only in memory have equal registers; `updatePub` makes the stored
`leftover` equal. `update_rel` with the continuation "both runs have returned" gives
`ct_subroutine_ok`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtUpdate

open Arm64 Arm64.Obj Poly1305DebianCt Leakage Poly1305DebianCtFw

theorem ctInternalOk_poly1305_update_dev :
    ctInternalOk "poly1305_update [libsodium_la_poly1305_donna]" updateIntPre updatePub := by
  refine ⟨by decide, ?_⟩
  intro pl hP _ X _ _ _
  intro x₁ x₂ R₁ R₂ s₁ s₂ he1 he2 hl1 hl2 hp1 hp2 hsame hpub
  obtain ⟨ro₁, st₁, msg₁⟩ := x₁
  obtain ⟨ro₂, st₂, msg₂⟩ := x₂
  obtain ⟨hpc₁, hrun₁, hal₁⟩ := he1
  obtain ⟨hpc₂, hrun₂, -⟩ := he2
  have e2 := sameExceptMem_eq hsame
  have hlr : s₁.readReg64 Reg.lr = s₂.readReg64 Reg.lr := by rw [e2]; rfl
  have hsp : s₁.sp = s₂.sp := by rw [e2]
  have hx0 : s₁.readReg64 Reg.x0 = s₂.readReg64 Reg.x0 := by rw [e2]; rfl
  have hx1 : s₁.readReg64 Reg.x1 = s₂.readReg64 Reg.x1 := by rw [e2]; rfl
  have hx2 : s₁.readReg64 Reg.x2 = s₂.readReg64 Reg.x2 := by rw [e2]; rfl
  have hfa : libsodiumDebianOnetimeauthCtLib.fnAddr pl
      "poly1305_update [libsodium_la_poly1305_donna]" = pl.base + 688#64 := rfl
  rw [hfa] at hpc₁ hpc₂
  refine update_rel (stopCompat_sub hlr hsp) hP hrun₁ hrun₂ hpc₁ hpc₂ hl1 hl2 hal₁ hsp hx0 hx1 hx2
    hp1 hp2 hpub.2 ?_
  intro r₁ r₂ ps₁ ps₂ m₁ m₂ _ _ _ _ _ _ _ _
  exact oe_stop (Or.inl ⟨rfl, rfl, hrun₁⟩) (Or.inl ⟨rfl, rfl, hrun₂⟩)

end Poly1305DebianCtUpdate

end
end

section
open Poly1305DebianCt

theorem solution :
    ctInternalOk "poly1305_update [libsodium_la_poly1305_donna]" updateIntPre updatePub := by
  apply Poly1305DebianCtUpdate.ctInternalOk_poly1305_update_dev <;> assumption

end
