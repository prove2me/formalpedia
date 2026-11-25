-- Prove2me | solution 1 for Poly1305Debian.internalOk_poly1305_blocks_v2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-25T22:19:19.906783+00:00
-- url     : https://prove2.me/submissions/9cfd7e42-ebff-43cf-b748-97af8c613d82

import Definitions.Def_Poly1305Debian_BlocksWhole
import Definitions.Def_Poly1305Debian_PlacedObj
import Definitions.Def_Poly1305Debian_Spec
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Definitions.Def_Poly1305Libsodium_Spec
import Mathlib.Tactic.ClearExcept

section
section
/-! Draft of the corrected M1 contract (not published): `blocksSpec` with `|m| % 16 = 0`.
Debian's GCC `poly1305_blocks` loops until `x1 = m + bytes`, so it needs `bytes` a positive
multiple of 16 (the published `blocksSpec` admits any `bytes ≥ 16` and is false at 17). -/

namespace Poly1305Debian

open Arm64 Arm64.Obj Poly1305Boringssl
open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

def blocksSpecV2 : Spec (Bool × List (BitVec 8) × BitVec 8 × List (BitVec 8)) where
  pre g s0 :=
    match g with
    | (ro, rh, fin, m) =>
      ⌜StateOk rh ∧ (s0.readReg64 Reg.x2).toNat = m.length ∧ 16 ≤ m.length ∧ m.length % 16 = 0⌝ ∗
        (s0.readReg64 Reg.x0 ↦ₛ rh) ∗ ((s0.readReg64 Reg.x0 + 88#64) ↦ₛ [fin]) ∗
        bytesIn ro (s0.readReg64 Reg.x1) m
  post := blocksSpec.post

end Poly1305Debian

end
end

section
section
/-! # Instruction fetch for the placed `libsodiumDebianOnetimeauth` text block -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.BlocksV2

open Arm64 Arm64.Obj

/-- The placed program the goal talks about, with extern hooks `X`. -/
def prog (pl : Placement) (X : String → Option (State → State)) : Program :=
  libsodiumDebianOnetimeauthLib.program pl X

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
theorem code_length : libsodiumDebianOnetimeauthPlacedCode.length = 1800 := by rfl

theorem patched_length (pl : Placement) : (libsodiumDebianOnetimeauthText.patched pl).length = 1800 := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE]
  show (List.map (fun _ => 4) (List.range (libsodiumDebianOnetimeauthPlacedCode.length / 4))).sum = 1800
  rw [code_length]; rfl

theorem hook_none {pl : Placement} (hP : libsodiumDebianOnetimeauthLib.Placeable pl)
    (X : String → Option (State → State)) {off : Nat} (hoff : off < 1800) :
    (prog pl X).externAt? (pl.base + BitVec.ofNat 64 off) = none := by
  have hl : libsodiumDebianOnetimeauthText.code.length = 1800 := code_length
  have e1 := (hP.text.externs_ok "__stack_chk_fail" (by decide)).2
  have e2 := (hP.text.externs_ok "crypto_verify_16" (by decide)).2
  have e3 := (hP.text.externs_ok "memset" (by decide)).2
  have e4 := (hP.text.externs_ok "randombytes_buf" (by decide)).2
  have e5 := (hP.text.externs_ok "sodium_memzero" (by decide)).2
  rw [show libsodiumDebianOnetimeauthLib.text = libsodiumDebianOnetimeauthText from rfl, hl]
    at e1 e2 e3 e4 e5
  have hpc : (pl.base + BitVec.ofNat 64 off - pl.base).toNat = off := by
    rw [show pl.base + BitVec.ofNat 64 off - pl.base = BitVec.ofNat 64 off by bv_omega,
      BitVec.toNat_ofNat]; omega
  simp only [prog, Program.externAt?, Program.hookAtOff?, PlacedLib.program, hpc]
  rw [show libsodiumDebianOnetimeauthLib.text.externs =
    ["__stack_chk_fail", "crypto_verify_16", "memset", "randombytes_buf", "sodium_memzero"] from rfl]
  simp only [List.map_cons, List.map_nil, List.findSome?_cons, List.findSome?_nil, ite_self,
    beq_iff_eq]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

/-- Byte `k < 4` of the word at aligned offset `off` of the placed code. -/
theorem read8_code {pl : Placement} {m : Memory} {X : String → Option (State → State)}
    (hCL : (prog pl X).CodeLoaded m) {off k : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 1800) (hk : k < 4) :
    m.read8 (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      (libsodiumDebianOnetimeauthText.patchedWord pl off).extractLsb' (8 * k) 8 ∧
    m.perm (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
  have hl : (prog pl X).code.length = 1800 := patched_length pl
  have h := codeLoaded_cell hCL (off + k) (by omega)
  have ha : pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
      (prog pl X).base + BitVec.ofNat 64 (off + k) := by
    show _ = pl.base + _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [ha]
  refine ⟨?_, h.2⟩
  rw [h.1]
  have ht := take4_drop_patched (blk := libsodiumDebianOnetimeauthText) (pl := pl) hal
    (by rw [show libsodiumDebianOnetimeauthText.code = libsodiumDebianOnetimeauthPlacedCode from rfl,
      code_length]; exact hlen)
  have e1 : (prog pl X).code[off + k]'(by omega) =
      (((libsodiumDebianOnetimeauthText.patched pl).drop off).take 4)[k]'(by
        simp [List.length_take, List.length_drop, patched_length]; omega) := by
    simp only [List.getElem_take, List.getElem_drop]; rfl
  rw [e1]
  simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * k + i < 32 := by omega
  simp [hi, this]; omega

theorem fetch_word {pl : Placement} {m : Memory} (hP : libsodiumDebianOnetimeauthLib.Placeable pl)
    {X : String → Option (State → State)} (hCL : (prog pl X).CodeLoaded m) {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 1800) :
    (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      decode (libsodiumDebianOnetimeauthText.patchedWord pl off) := by
  have hb4 : pl.base.toNat % 4 = 0 := by
    have := hP.text.base_aligned
    rw [show libsodiumDebianOnetimeauthLib.text.align = 32 from rfl] at this
    omega
  have hnw : pl.base.toNat + 1800 ≤ 2 ^ 64 := by
    have := hP.text.no_wrap
    have hl : libsodiumDebianOnetimeauthText.code.length = 1800 := code_length
    rw [show libsodiumDebianOnetimeauthLib.text = libsodiumDebianOnetimeauthText from rfl, hl] at this
    exact this
  have hpc : (pl.base + BitVec.ofNat 64 off).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : off % 2 ^ 64 = off := Nat.mod_eq_of_lt (by omega)
    have h2 : (pl.base.toNat + off) % 2 ^ 64 = pl.base.toNat + off := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]; omega
  have hlen' : off < 1800 := by omega
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

end Poly1305Debian.BlocksV2

end
end

section
section
/-! # Abstract machine states and single-step plumbing

Every state reached by `poly1305_blocks` is `mkS s0 pc sp m ps r`: the entry state `s0` with
`pc`, `sp`, memory `m`, flags `ps` and the registers `x1..x17` (given by `r k` for `1 ≤ k ≤ 17`)
replaced. `x0`, `x18..x30` and everything else stay those of `s0`. -/

set_option autoImplicit false

namespace Poly1305Debian.BlocksV2

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

end Poly1305Debian.BlocksV2

end
end

section
section
/-! # Memory: byte writes, the written region, and the memory invariant `MemOk`

The routine writes only the accumulator bytes `[x0 + 24, x0 + 48)` (the region `W`). `MemOk s0 m`: every cell outside `W` is that of `s0.mem`, and
every byte of `W` is mapped read-write (not lazy-free, anonymity unchanged), as in `s0.mem`. -/

set_option autoImplicit false

namespace Poly1305Debian.BlocksV2

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

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
  libsodiumDebianOnetimeauthLib.Placeable pl ∧ (prog pl X).CodeLoaded s0.mem ∧ MemOk s0 m

theorem Good.codeLoaded {pl : Placement} {X : String → Option (State → State)} {s0 : State} {m : Memory}
    (hg : Good pl X s0 m) : (prog pl X).CodeLoaded m :=
  codeLoaded_of hg.2.1 fun a ha => hg.2.2.1 a fun hw => by
    have := (hg.2.2.2 a hw).2.2.2; rw [ha] at this; cases this

theorem Good.write8 {pl : Placement} {X : String → Option (State → State)} {s0 : State} {m : Memory}
    (hg : Good pl X s0 m) {a : BitVec 64} (ha : W s0 a) (v : BitVec 8) : Good pl X s0 (m.write8 a v) :=
  ⟨hg.1, hg.2.1, memOk_write8 hg.2.2 ha v⟩

end Poly1305Debian.BlocksV2

end
end

section
section
/-! # The instruction at each address of `poly1305_blocks` (text offsets 0x1a0..0x2ac)

Each lemma is `rfl` after `fetch_word` and `patchedWord_plain` (no relocation lies inside the
function). Lemma `f_<k>` is function offset `k` (hex). -/

set_option autoImplicit false

namespace Poly1305Debian.BlocksV2

open Arm64 Arm64.Obj

set_option maxRecDepth 100000

theorem patchedWord_plain (pl : Placement) {off : Nat}
    (h : libsodiumDebianOnetimeauthText.relocAt? off = none) :
    libsodiumDebianOnetimeauthText.patchedWord pl off = libsodiumDebianOnetimeauthText.wordAt off := by
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

end Poly1305Debian.BlocksV2

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

namespace Poly1305Debian.BlocksV2

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Arm64.Obj

def Reach (pl : Placement) (X : String → Option (State → State)) (Q : State → Prop) (s : State) :
    Prop :=
  ∃ sf, Steps (prog pl X) s sf ∧ Q sf

theorem reach_step {pl : Placement} {X : String → Option (State → State)} {Q : State → Prop}
    {s s' : State} (h : Step (prog pl X) s s') (h' : Reach pl X Q s') : Reach pl X Q s := by
  obtain ⟨sf, h1, h2⟩ := h'
  exact ⟨sf, Steps.step h h1, h2⟩

theorem reach_done {pl : Placement} {X : String → Option (State → State)} {Q : State → Prop}
    {s : State} (h : Q s) : Reach pl X Q s :=
  ⟨s, Steps.refl _, h⟩

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

/-- The carry flag of a 64-bit addition. -/
def addC (x y : Nat) : Bool := decide (2 ^ 64 ≤ x + y)

/-- The value of the carry flag as a number. -/
def cv (b : Bool) : Nat := if b then 1 else 0

theorem extr_nat (n k lsb : Nat) (h : lsb ≤ 64) :
    (n * 2 ^ 64 + k) / 2 ^ lsb = k / 2 ^ lsb + n * 2 ^ (64 - lsb) := by
  have e : 2 ^ 64 = 2 ^ lsb * 2 ^ (64 - lsb) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.add_comm, Nat.mul_left_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]

variable {pl : Placement} {X : String → Option (State → State)} {Q : State → Prop} {s0 : State}
  {pc sp : BitVec 64} {m : Memory} {ps : PState} {r : Nat → BitVec 64}

/-! ## Arithmetic and logic -/

/-- `add xd, xn, xm, lsl #a`. -/
theorem r_addLsl {d n k : BitVec 5} {a : Nat} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSL a))
    (ha : a < 64 := by decide)
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + (r k.toNat).toNat * 2 ^ a))))) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_addSubShift]
  simp only [execAddSubShift, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalAddSub, State.writeReg, shiftVal, shift64]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC, Bool.false_eq_true, if_false]
  refine mkS_upd_congr ?_
  simp [AddWithCarry64, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt ha]
  omega

/-- `add xd, xn, xm, lsr #a`. -/
theorem r_addLsr {d n k : BitVec 5} {a : Nat} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSR a))
    (ha : a < 64 := by decide)
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + (r k.toNat).toNat / 2 ^ a))))) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
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

/-- `adds xd, xn, xm`: the carry flag is `addC`. -/
theorem r_adds {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubShift .W64 .ADDS (.gpr d) (.gpr n) (.gpr k) .LSL 0))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide)
    (h : ∀ ps' : PState, ps'.c = addC (r n.toNat).toNat (r k.toNat).toNat →
      Reach pl X Q (mkS s0 (pc + 4#64) sp m ps'
        (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + (r k.toNat).toNat))))) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) (h (AddWithCarry64 (r n.toNat) (r k.toNat) false).2 ?_)
  · rw [ex_addSubShift]
    simp only [execAddSubShift, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
      evalAddSub, State.writeReg, shiftVal, shift64, Nat.zero_mod, BitVec.shiftLeft_zero]
    simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_setPState, mkS_advancePC]
    refine mkS_upd_congr ?_
    simp [AddWithCarry64, BitVec.toNat_add, BitVec.toNat_setWidth]
    omega
  · have hx := (r n.toNat).isLt
    have hy := (r k.toNat).isLt
    simp [AddWithCarry64, addC, BitVec.msb_eq_decide, BitVec.toNat_add, BitVec.toNat_setWidth]
    omega

/-- `adc xd, xn, xm`. -/
theorem r_adc {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubCarry .W64 .ADD (.gpr d) (.gpr n) (.gpr k)))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + (r k.toNat).toNat + cv ps.c))))) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_addSubCarry]
  simp only [execAddSubCarry, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    evalAddSub, State.writeReg, mkS_pstate]
  simp only [wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC, Bool.false_eq_true, if_false]
  refine mkS_upd_congr ?_
  cases ps.c <;> simp [AddWithCarry64, BitVec.toNat_add, BitVec.toNat_setWidth, cv] <;> omega

/-- `cinc xd, xn, hs` (`csinc xd, xn, xn, lo`). -/
theorem r_cinc {d n : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.condSelect .W64 .CSINC (.gpr d) (.gpr n) (.gpr n) .CC))
    (hd : Ok d := by decide) (hn : Ok n := by decide)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat + cv ps.c))))) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_condSelect]
  simp only [execCondSelect, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, mkS_pstate, ConditionHolds]
  cases ps.c <;> simp [wr_gpr _ _ _ _ _ _ _ hd, State.writeReg, cv] <;> refine mkS_upd_congr ?_ <;>
    simp [BitVec.toNat_add]

/-- `mul xd, xn, xm` (`madd xd, xn, xm, xzr`). -/
theorem r_mul {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.dataProc3 .W64 .MADD (.gpr d) (.gpr n) (.gpr k) .xzr))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat * (r k.toNat).toNat))))) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_dataProc3]
  simp only [execDataProc3, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk, rd_xzr,
    State.writeReg, wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  refine mkS_upd_congr ?_
  simp [BitVec.toNat_mul]

/-- `umulh xd, xn, xm`. -/
theorem r_umulh {d n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.dataProc3 .W64 .UMULH (.gpr d) (.gpr n) (.gpr k) .xzr))
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat * (r k.toNat).toNat / 2 ^ 64))))) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
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
theorem r_extr {d n k : BitVec 5} {lsb : Nat} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.extr .W64 (.gpr d) (.gpr n) (.gpr k) lsb))
    (hl : 0 < lsb ∧ lsb < 64 := by decide)
    (hd : Ok d := by decide) (hn : Ok n := by decide) (hk : Ok k := by decide)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64
        ((r k.toNat).toNat / 2 ^ lsb + (r n.toNat).toNat * 2 ^ (64 - lsb)))))) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_extr]
  simp only [State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
    State.writeReg, wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  refine mkS_upd_congr ?_
  have hk' := (r k.toNat).isLt
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl.2, Nat.shiftRight_eq_div_pow]
  rw [← Nat.shiftLeft_add_eq_or_of_lt hk', Nat.shiftLeft_eq, extr_nat _ _ _ hl.2.le]

/-- `and xd, xn, #(2^k - 1)`. -/
theorem r_andMask {d n : BitVec 5} {mask : BitVec 64} (k : Nat) (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.logicalImm .W64 .AND (.gpr d) (.gpr n) mask))
    (hm : mask = BitVec.ofNat 64 (2 ^ k - 1) := by decide) (hk : k < 64 := by decide)
    (hd : Ok d := by decide) (hn : Ok n := by decide)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat % 2 ^ k))))) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  subst hm
  refine reach_step (step_mkS hrun hf ?_) h
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
theorem r_lsl2 {d n : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.bitfield .W64 .UBFM (.gpr d) (.gpr n) 62 61))
    (hd : Ok d := by decide) (hn : Ok n := by decide)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 ((r n.toNat).toNat * 4))))) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_bitfield]
  simp only [execBitfield, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, evalBitfield, State.writeReg,
    wr_gpr _ _ _ _ _ _ _ hd, mkS_advancePC]
  simp only [Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, beq_self_eq_true, Bool.and_self, if_true,
    show (BitfieldOp.UBFM == BitfieldOp.UBFM) = true from rfl]
  simp
  refine mkS_upd_congr ?_
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- `cmp wn, #0`: the zero flag says whether the low 32 bits of `xn` vanish. -/
theorem r_cmpW0 {n : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubImm .W32 .SUBS .xzr (.gpr n) 0x000#12 false))
    (hn : Ok n := by decide)
    (h : ∀ ps' : PState, ps'.z = decide ((r n.toNat).toNat % 2 ^ 32 = 0) →
      Reach pl X Q (mkS s0 (pc + 4#64) sp m ps' r)) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) (h (AddWithCarry32 ((r n.toNat).setWidth 32)
    (~~~((0x000#12).setWidth 64 : BitVec 64).setWidth 32) true).2 ?_)
  · rw [ex_addSubImm]
    simp only [execAddSubImm, State.readReg, State.readReg32, rd_gpr _ _ _ _ _ _ _ hn, evalAddSub,
      State.writeReg, wr_xzr, mkS_setPState, mkS_advancePC]
    simp [BitVec.toNat_setWidth]
  · simp only [AddWithCarry32]
    have e : decide ((r n.toNat).toNat % 2 ^ 32 = 0) = ((r n.toNat).setWidth 32 == 0#32) := by
      rw [Bool.eq_iff_iff]; simp [← BitVec.toNat_inj, BitVec.toNat_setWidth]
    rw [e, Bool.eq_iff_iff]; simp; bv_omega

/-! ## Branches -/

theorem r_bCond_t {c : CondCode} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.bCond c off)) (hc : ConditionHolds c ps = true)
    (h : Reach pl X Q (mkS s0 (pc + off) sp m ps r)) : Reach pl X Q (mkS s0 pc sp m ps r) :=
  reach_step (step_mkS hrun hf (by rw [ex_bCond]; simp [hc])) h

theorem r_bCond_f {c : CondCode} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.bCond c off)) (hc : ConditionHolds c ps = false)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp m ps r)) : Reach pl X Q (mkS s0 pc sp m ps r) :=
  reach_step (step_mkS hrun hf (by rw [ex_bCond]; simp [hc])) h

theorem r_ret (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ret (.gpr 0x1e#5)))
    (h : Reach pl X Q (mkS s0 (s0.readReg64 (.gpr 0x1e#5)) sp m ps r)) :
    Reach pl X Q (mkS s0 pc sp m ps r) :=
  reach_step (step_mkS hrun hf (by
    rw [ex_ret, rd_hi _ _ _ _ _ _ _ (by decide)]; simp)) h

/-! ## Loads and stores (64-bit) -/

/-- `ldp xt1, xt2, [xb, #off]`. -/
theorem r_ldp64 {t1 t2 b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ldp .W64 false (.gpr t1) (.gpr t2) (.Offset (.gpr b) off)))
    (hb : b ≠ 31#5 := by decide)
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hr1 : m.canRead a 8 = true) (hr2 : m.canRead (a + 8#64) 8 = true)
    (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp m ps
      (upd (upd r t1.toNat (m.read64 a)) t2.toNat (m.read64 (a + 8#64))))) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_ldp]
  simp only [execLdp, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hr1, hr2, Bool.and_self,
    MemWidth.bytes, Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ h1,
    wr_gpr _ _ _ _ _ _ _ h2, mkS_advancePC]

/-- `ldp xt1, xt2, [xb], #16` (post-index; `b ∉ {t1, t2}`). -/
theorem r_ldpPost {t1 t2 b : BitVec 5} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ldp .W64 false (.gpr t1) (.gpr t2) (.PostIndex (.gpr b) off)))
    (hr1 : m.canRead (r b.toNat) 8 = true) (hr2 : m.canRead (r b.toNat + 8#64) 8 = true)
    (hb : Ok b := by decide) (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp m ps
      (upd (upd (upd r b.toNat (r b.toNat + off)) t1.toNat (m.read64 (r b.toNat))) t2.toNat
        (m.read64 (r b.toNat + 8#64))))) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_ldp]
  simp only [execLdp, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, rd_gpr _ _ _ _ _ _ _ hb, hr1, hr2,
    Bool.and_self, MemWidth.bytes, Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ hb,
    wr_gpr _ _ _ _ _ _ _ h1, wr_gpr _ _ _ _ _ _ _ h2, mkS_advancePC]

/-- `ldrb wt, [xb, #off]`. -/
theorem r_ldrb {t b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ldr .W32 .B8 false (.gpr t) (.Offset (.gpr b) off)))
    (hb : b ≠ 31#5 := by decide)
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hr : m.canRead a 1 = true) (ht : Ok t := by decide)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp m ps (upd r t.toNat (BitVec.ofNat 64 (m.read8 a).toNat)))) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_ldr]
  simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hr,
    MemWidth.bytes, Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ ht, mkS_advancePC]
  refine mkS_upd_congr ?_
  simp [BitVec.toNat_setWidth]

/-- `stp xt1, xt2, [xb, #off]`. -/
theorem r_stp64 {t1 t2 b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.stp .W64 (.gpr t1) (.gpr t2) (.Offset (.gpr b) off)))
    (hb : b ≠ 31#5 := by decide)
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hw1 : m.canWrite a 8 = true) (hw2 : m.canWrite (a + 8#64) 8 = true)
    (h1 : Ok t1 := by decide) (h2 : Ok t2 := by decide)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp
      ((m.write64 a (r t1.toNat)).write64 (a + 8#64) (r t2.toNat)) ps r)) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_stp]
  simp only [execStp, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hw1, hw2, Bool.and_self,
    MemWidth.bytes, Memory.writeSized, rd_gpr _ _ _ _ _ _ _ h1, rd_gpr _ _ _ _ _ _ _ h2,
    mkS_setMem, mkS_advancePC]

/-- `str xt, [xb, #off]`. -/
theorem r_str64 {t b : BitVec 5} {off a : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.str .X64 (.gpr t) (.Offset (.gpr b) off)))
    (hb : b ≠ 31#5 := by decide)
    (ha : (mkS s0 pc sp m ps r).readReg64 (.gpr b) + off = a)
    (hw : m.canWrite a 8 = true) (ht : Ok t := by decide)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp (m.write64 a (r t.toNat)) ps r)) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_str]
  simp only [execStr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, mkS_mem, ha, hw,
    MemWidth.bytes, Memory.writeSized, rd_gpr _ _ _ _ _ _ _ ht, mkS_setMem, mkS_advancePC]

/-! ## Instructions only the GCC build uses -/

/-- `cset xd, eq` (`csinc xd, xzr, xzr, ne`). -/
theorem r_cset {d : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.condSelect .W64 .CSINC (.gpr d) .xzr .xzr .NE))
    (hd : Ok d := by decide)
    (h : Reach pl X Q (mkS s0 (pc + 4#64) sp m ps
      (upd r d.toNat (BitVec.ofNat 64 (if ps.z then 1 else 0))))) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) h
  rw [ex_condSelect]
  simp only [execCondSelect, State.readReg, rd_xzr, mkS_pstate, ConditionHolds]
  by_cases hz : ps.z = true <;> simp [hz, wr_gpr _ _ _ _ _ _ _ hd, State.writeReg]

/-- `cmp xn, xm`: the zero flag says whether the registers are equal. -/
theorem r_cmpReg {n k : BitVec 5} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubShift .W64 .SUBS .xzr (.gpr n) (.gpr k) .LSL 0))
    (hn : Ok n := by decide) (hk : Ok k := by decide)
    (h : ∀ ps' : PState, ps'.z = decide (r n.toNat = r k.toNat) →
      Reach pl X Q (mkS s0 (pc + 4#64) sp m ps' r)) :
    Reach pl X Q (mkS s0 pc sp m ps r) := by
  refine reach_step (step_mkS hrun hf ?_) (h (AddWithCarry64 (r n.toNat) (~~~(r k.toNat)) true).2 ?_)
  · rw [ex_addSubShift]
    simp only [execAddSubShift, State.readReg, rd_gpr _ _ _ _ _ _ _ hn, rd_gpr _ _ _ _ _ _ _ hk,
      evalAddSub, State.writeReg, shiftVal, shift64, Nat.zero_mod, BitVec.shiftLeft_zero]
    simp
  · simp only [AddWithCarry64]
    rw [Bool.eq_iff_iff]; simp; bv_omega

end Poly1305Debian.BlocksV2

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

namespace Poly1305Debian.BlocksV2

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)
open Poly1305Boringssl

section
variable (a0 a1 a2 r0 r1 r2 : Nat)

def D0 : Nat := a0 * r0 + a1 * (20 * r2) + a2 * (20 * r1)
def D1 : Nat := a0 * r1 + a1 * r0 + a2 * (20 * r2)
def D2 : Nat := a0 * r2 + a1 * r1 + a2 * r0
def E1 : Nat := D1 a0 a1 a2 r0 r1 r2 + D0 a0 a1 a2 r0 r1 r2 / 2 ^ 44
def E2 : Nat := D2 a0 a1 a2 r0 r1 r2 + E1 a0 a1 a2 r0 r1 r2 / 2 ^ 44
def F : Nat := 5 * (E2 a0 a1 a2 r0 r1 r2 / 2 ^ 42) + D0 a0 a1 a2 r0 r1 r2 % 2 ^ 44
def N0 : Nat := F a0 a1 a2 r0 r1 r2 % 2 ^ 44
def N1 : Nat := E1 a0 a1 a2 r0 r1 r2 % 2 ^ 44 + F a0 a1 a2 r0 r1 r2 / 2 ^ 44
def N2 : Nat := E2 a0 a1 a2 r0 r1 r2 % 2 ^ 42

end

/-- The new limbs represent `A * R` modulo `p = 2^130 - 5`. -/
theorem blk_mod (a0 a1 a2 r0 r1 r2 : Nat) :
    (N0 a0 a1 a2 r0 r1 r2 + 2 ^ 44 * N1 a0 a1 a2 r0 r1 r2 + 2 ^ 88 * N2 a0 a1 a2 r0 r1 r2) %
        p1305 =
      ((a0 + 2 ^ 44 * a1 + 2 ^ 88 * a2) * (r0 + 2 ^ 44 * r1 + 2 ^ 88 * r2)) % p1305 := by
  generalize hD0 : D0 a0 a1 a2 r0 r1 r2 = X0
  generalize hD1 : D1 a0 a1 a2 r0 r1 r2 = X1
  generalize hD2 : D2 a0 a1 a2 r0 r1 r2 = X2
  have hc : N0 a0 a1 a2 r0 r1 r2 + 2 ^ 44 * N1 a0 a1 a2 r0 r1 r2 + 2 ^ 88 * N2 a0 a1 a2 r0 r1 r2 +
      p1305 * (E2 a0 a1 a2 r0 r1 r2 / 2 ^ 42) = X0 + 2 ^ 44 * X1 + 2 ^ 88 * X2 := by
    simp only [N0, N1, N2, F, E2, E1, hD0, hD1, hD2, p1305]
    omega
  have hp : (a0 + 2 ^ 44 * a1 + 2 ^ 88 * a2) * (r0 + 2 ^ 44 * r1 + 2 ^ 88 * r2) =
      X0 + 2 ^ 44 * X1 + 2 ^ 88 * X2 +
      p1305 * (4 * (a1 * r2 + a2 * r1) + 2 ^ 44 * (4 * (a2 * r2))) := by
    subst hD0 hD1 hD2
    simp only [D0, D1, D2, p1305]
    rw [show (2 : Nat) ^ 130 - 5 = 1361129467683753853853498429727072845819 by norm_num]
    ring
  have key : ∀ L c E : Nat, (L + p1305 * c + p1305 * E) % p1305 = L % p1305 := by
    intro L c E; rw [Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left]
  rw [hp, ← hc, key]

/-- Size of the column sums (for exactness of the 128-bit arithmetic). -/
theorem blk_cols (a0 a1 a2 r0 r1 r2 : Nat) (k0 : r0 ≤ 0xffc0fffffff) (k1 : r1 ≤ 0xfffffc0ffff)
    (k2 : r2 ≤ 0xffffffc0f) (b0 : a0 < 2 ^ 45) (b1 : a1 < 2 ^ 45 + 64) (b2 : a2 < 2 ^ 42 + 2 ^ 41) :
    D0 a0 a1 a2 r0 r1 r2 < 2 ^ 100 ∧ D1 a0 a1 a2 r0 r1 r2 < 2 ^ 100 ∧
      D2 a0 a1 a2 r0 r1 r2 < 2 ^ 100 := by
  have m := fun {x y X Y : Nat} (hx : x ≤ X) (hy : y ≤ Y) => Nat.mul_le_mul hx hy
  have A0 : a0 ≤ 2 ^ 45 - 1 := by omega
  have A1 : a1 ≤ 2 ^ 45 + 63 := by omega
  have A2 : a2 ≤ 2 ^ 42 + 2 ^ 41 - 1 := by omega
  have S1 : 20 * r1 ≤ 20 * 0xfffffc0ffff := by omega
  have S2 : 20 * r2 ≤ 20 * 0xffffffc0f := by omega
  have := m A0 k0; have := m A0 k1; have := m A0 k2
  have := m A1 k0; have := m A1 k1; have := m A1 S2
  have := m A2 k0; have := m A2 S1; have := m A2 S2
  simp only [D0, D1, D2]
  omega

/-- The new limbs satisfy the `StateOk` bounds again. -/
theorem blk_bounds (a0 a1 a2 r0 r1 r2 : Nat) (k0 : r0 ≤ 0xffc0fffffff) (k1 : r1 ≤ 0xfffffc0ffff)
    (k2 : r2 ≤ 0xffffffc0f) (b0 : a0 < 2 ^ 45) (b1 : a1 < 2 ^ 45 + 64) (b2 : a2 < 2 ^ 42 + 2 ^ 41) :
    N0 a0 a1 a2 r0 r1 r2 < 2 ^ 44 ∧ N1 a0 a1 a2 r0 r1 r2 < 2 ^ 44 + 64 ∧
      N2 a0 a1 a2 r0 r1 r2 < 2 ^ 42 := by
  have m := fun {x y X Y : Nat} (hx : x ≤ X) (hy : y ≤ Y) => Nat.mul_le_mul hx hy
  have A0 : a0 ≤ 2 ^ 45 - 1 := by omega
  have A1 : a1 ≤ 2 ^ 45 + 63 := by omega
  have A2 : a2 ≤ 2 ^ 42 + 2 ^ 41 - 1 := by omega
  have S1 : 20 * r1 ≤ 20 * 0xfffffc0ffff := by omega
  have S2 : 20 * r2 ≤ 20 * 0xffffffc0f := by omega
  have := m A0 k0; have := m A0 k1; have := m A0 k2
  have := m A1 k0; have := m A1 k1; have := m A1 S2
  have := m A2 k0; have := m A2 S1; have := m A2 S2
  simp only [N0, N1, N2, F, E2, E1, D0, D1, D2]
  omega

end Poly1305Debian.BlocksV2

end
end

section
section
/-! # Chain helpers: pc normalization, naming computed values, carries as numbers -/

set_option autoImplicit false

namespace Poly1305Debian.BlocksV2

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Arm64.Obj

/-- Normalizing `pc` after a step. -/
theorem nx {pl : Placement} {X : String → Option (State → State)} {Q : State → Prop} {s0 : State}
    {sp : BitVec 64} {m : Memory} {ps : PState} {r : Nat → BitVec 64} (b : BitVec 64) (x y : Nat)
    (hxy : x + 4 = y := by decide)
    (h : Reach pl X Q (mkS s0 (b + BitVec.ofNat 64 y) sp m ps r)) :
    Reach pl X Q (mkS s0 (b + BitVec.ofNat 64 x + 4#64) sp m ps r) := by
  rw [pc_add, hxy]; exact h

/-- Name the value just written to a register (keeps terms linear in size). -/
theorem reach_gen {pl : Placement} {X : String → Option (State → State)} {Q : State → Prop}
    {s0 : State} {pc sp : BitVec 64} {m : Memory} {ps : PState} {r : Nat → BitVec 64} {k : Nat}
    {v : BitVec 64} (h : ∀ w, w = v → Reach pl X Q (mkS s0 pc sp m ps (upd r k w))) :
    Reach pl X Q (mkS s0 pc sp m ps (upd r k v)) := h v rfl

theorem toNat_eq_of {v : BitVec 64} {E : Nat} (h : v = BitVec.ofNat 64 E) : v.toNat = E % 2 ^ 64 := by
  subst h; simp

theorem cv_addC {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : cv (addC x y) = (x + y) / 2 ^ 64 := by
  unfold cv addC
  by_cases h : 2 ^ 64 ≤ x + y
  · rw [decide_eq_true h, if_pos rfl]
    have h1 : 1 ≤ (x + y) / 2 ^ 64 := (Nat.le_div_iff_mul_le (by decide)).2 (by omega)
    have h2 : (x + y) / 2 ^ 64 < 2 := (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega)
    omega
  · rw [decide_eq_false h, if_neg (by decide)]
    exact (Nat.div_eq_of_lt (by omega)).symm

theorem cv_of_eq {b : Bool} {x y : Nat} (h : b = addC x y) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    cv b = (x + y) / 2 ^ 64 := by rw [h]; exact cv_addC hx hy

end Poly1305Debian.BlocksV2

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

namespace Poly1305Debian.BlocksV2

open Arm64 Arm64.Obj

/-- The limbs of `h + block + hibit` the iteration multiplies. -/
def la0 (H0 T0 : Nat) : Nat := H0 + T0 % 2 ^ 44
def la1 (H1 T0 T1 : Nat) : Nat := H1 + (T0 / 2 ^ 44 + T1 * 2 ^ 20) % 2 ^ 44
def la2 (H2 HB T1 : Nat) : Nat := H2 + HB + T1 / 2 ^ 24

/-- What the iteration leaves. -/
def BodyPost (r r' : Nat → BitVec 64) (P : BitVec 64) (H0 H1 H2 HB T0 T1 R0 R1 R2 : Nat) : Prop :=
  r' 1 = P + 16#64 ∧ r' 2 = r 2 ∧
  r' 8 = r 8 ∧ r' 9 = r 9 ∧ r' 10 = r 10 ∧ r' 11 = r 11 ∧ r' 12 = r 12 ∧ r' 13 = r 13 ∧
  (r' 7).toNat = N0 (la0 H0 T0) (la1 H1 T0 T1) (la2 H2 HB T1) R0 R1 R2 ∧
  (r' 3).toNat = N1 (la0 H0 T0) (la1 H1 T0 T1) (la2 H2 HB T1) R0 R1 R2 ∧
  (r' 15).toNat = N2 (la0 H0 T0) (la1 H1 T0 T1) (la2 H2 HB T1) R0 R1 R2

theorem mul_lt_128 {a b : Nat} (ha : a < 2 ^ 46) (hb : b < 2 ^ 50) : a * b < 2 ^ 128 :=
  calc a * b < 2 ^ 46 * 2 ^ 50 := Nat.mul_lt_mul'' ha hb
    _ ≤ 2 ^ 128 := by norm_num

theorem mul128 {lo hi : BitVec 64} {P : Nat} (hl : lo.toNat = P % 2 ^ 64)
    (hh : hi.toNat = P / 2 ^ 64 % 2 ^ 64) (hP : P < 2 ^ 128) : lo.toNat + 2 ^ 64 * hi.toNat = P := by
  omega

/-- A 128-bit addition by `adds`/`adc`: `(xl, xh) + (yl, yh)` without overflow. -/
theorem add128 {zl zh : BitVec 64} {xl xh yl yh : Nat} {c : Bool}
    (hl : zl.toNat = (xl + yl) % 2 ^ 64) (hh : zh.toNat = (xh + yh + cv c) % 2 ^ 64)
    (hc : c = addC xl yl) (hb : xl < 2 ^ 64 ∧ yl < 2 ^ 64 ∧ xl + yl + 2 ^ 64 * (xh + yh) < 2 ^ 128) :
    zl.toNat + 2 ^ 64 * zh.toNat = xl + yl + 2 ^ 64 * (xh + yh) := by
  rw [cv_of_eq hc hb.1 hb.2.1] at hh
  omega

/-- A 128-bit addition by `adds`/`cinc` (one summand is a single word). -/
theorem add128c {zl zh : BitVec 64} {xl yl xh : Nat} {c : Bool}
    (hl : zl.toNat = (xl + yl) % 2 ^ 64) (hh : zh.toNat = (xh + cv c) % 2 ^ 64)
    (hc : c = addC xl yl) (hb : xl < 2 ^ 64 ∧ yl < 2 ^ 64 ∧ xl + yl + 2 ^ 64 * xh < 2 ^ 128) :
    zl.toNat + 2 ^ 64 * zh.toNat = xl + yl + 2 ^ 64 * xh := by
  rw [cv_of_eq hc hb.1 hb.2.1] at hh
  omega

/-- `extr #44` of a 128-bit value below `2^108`. -/
theorem extr128 {v : BitVec 64} {lo hi : Nat}
    (h : v.toNat = (lo / 17592186044416 + hi * 2 ^ (64 - 44)) % 2 ^ 64) (hb : lo + 2 ^ 64 * hi < 2 ^ 108)
    (hlo : lo < 2 ^ 64 := by omega) : v.toNat = (lo + 2 ^ 64 * hi) / 2 ^ 44 := by
  simp only [Nat.reduceSub] at h
  omega

/-- `extr #42` of a 128-bit value below `2^106`. -/
theorem extr128' {v : BitVec 64} {lo hi : Nat}
    (h : v.toNat = (lo / 4398046511104 + hi * 2 ^ (64 - 42)) % 2 ^ 64) (hb : lo + 2 ^ 64 * hi < 2 ^ 106)
    (hlo : lo < 2 ^ 64 := by omega) : v.toNat = (lo + 2 ^ 64 * hi) / 2 ^ 42 := by
  simp only [Nat.reduceSub] at h
  omega

set_option maxHeartbeats 4000000 in
theorem bodySeg {pl : Placement} {X : String → Option (State → State)} {Q : State → Prop}
    {s0 : State} {sp : BitVec 64} {m : Memory} {ps : PState} {r : Nat → BitVec 64}
    (hrun : s0.status = .Running) (hg : Good pl X s0 m)
    {P : BitVec 64} (hx1 : r 1 = P)
    (hr1 : m.canRead (r 1) 8 = true) (hr2 : m.canRead (r 1 + 8#64) 8 = true)
    {H0 H1 H2 HF R0 R1 R2 : Nat}
    (h7 : (r 7).toNat = H0) (h3 : (r 3).toNat = H1) (h15 : (r 15).toNat = H2)
    (h13 : (r 13).toNat = HF) (h8 : (r 8).toNat = R0) (h9 : (r 9).toNat = R1)
    (h12 : (r 12).toNat = R2) (h11 : (r 11).toNat = 20 * R1) (h10 : (r 10).toNat = 20 * R2)
    (bH0 : H0 < 2 ^ 44) (bH1 : H1 < 2 ^ 44 + 64) (bH2 : H2 < 2 ^ 42) (bHF : HF ≤ 1)
    (k0 : R0 ≤ 0xffc0fffffff) (k1 : R1 ≤ 0xfffffc0ffff) (k2 : R2 ≤ 0xffffffc0f)
    (k : ∀ (r' : Nat → BitVec 64) (ps' : PState),
      BodyPost r r' P H0 H1 H2 (HF * 2 ^ 40) (m.read64 P).toNat (m.read64 (P + 8#64)).toNat R0 R1 R2 →
      Reach pl X Q (mkS s0 (pl.base + 668#64) sp m ps' r')) :
    Reach pl X Q (mkS s0 (pl.base + 460#64) sp m ps r) := by
  refine r_ldpPost hrun (f_2c hg) hr1 hr2 (h := ?_)
  refine nx pl.base 460 464 (h := ?_)
  refine reach_gen fun v2c e2c => ?_
  refine r_andMask 44 hrun (f_30 hg) (h := ?_)
  refine nx pl.base 464 468 (h := ?_)
  refine reach_gen fun v30 e30 => ?_
  refine r_extr hrun (f_34 hg) (h := ?_)
  refine nx pl.base 468 472 (h := ?_)
  refine reach_gen fun v34 e34 => ?_
  refine r_andMask 44 hrun (f_38 hg) (h := ?_)
  refine nx pl.base 472 476 (h := ?_)
  refine reach_gen fun v38 e38 => ?_
  refine r_extr hrun (f_3c hg) (h := ?_)
  refine nx pl.base 476 480 (h := ?_)
  refine reach_gen fun v3c e3c => ?_
  refine r_addLsl hrun (f_40 hg) (h := ?_)
  refine nx pl.base 480 484 (h := ?_)
  refine reach_gen fun v40 e40 => ?_
  refine r_addLsl hrun (f_44 hg) (h := ?_)
  refine nx pl.base 484 488 (h := ?_)
  refine reach_gen fun v44 e44 => ?_
  refine r_addLsl hrun (f_48 hg) (h := ?_)
  refine nx pl.base 488 492 (h := ?_)
  refine reach_gen fun v48 e48 => ?_
  refine r_mul hrun (f_4c hg) (h := ?_)
  refine nx pl.base 492 496 (h := ?_)
  refine reach_gen fun v4c e4c => ?_
  refine r_mul hrun (f_50 hg) (h := ?_)
  refine nx pl.base 496 500 (h := ?_)
  refine reach_gen fun v50 e50 => ?_
  refine r_umulh hrun (f_54 hg) (h := ?_)
  refine nx pl.base 500 504 (h := ?_)
  refine reach_gen fun v54 e54 => ?_
  refine r_mul hrun (f_58 hg) (h := ?_)
  refine nx pl.base 504 508 (h := ?_)
  refine reach_gen fun v58 e58 => ?_
  refine r_adds hrun (f_5c hg) (h := fun ps5c c5c => ?_)
  refine nx pl.base 508 512 (h := ?_)
  refine reach_gen fun v5c e5c => ?_
  refine r_umulh hrun (f_60 hg) (h := ?_)
  refine nx pl.base 512 516 (h := ?_)
  refine reach_gen fun v60 e60 => ?_
  refine r_umulh hrun (f_64 hg) (h := ?_)
  refine nx pl.base 516 520 (h := ?_)
  refine reach_gen fun v64 e64 => ?_
  refine r_adc hrun (f_68 hg) (h := ?_)
  refine nx pl.base 520 524 (h := ?_)
  refine reach_gen fun v68 e68 => ?_
  refine r_adds hrun (f_6c hg) (h := fun ps6c c6c => ?_)
  refine nx pl.base 524 528 (h := ?_)
  refine reach_gen fun v6c e6c => ?_
  refine r_mul hrun (f_70 hg) (h := ?_)
  refine nx pl.base 528 532 (h := ?_)
  refine reach_gen fun v70 e70 => ?_
  refine r_adc hrun (f_74 hg) (h := ?_)
  refine nx pl.base 532 536 (h := ?_)
  refine reach_gen fun v74 e74 => ?_
  refine r_mul hrun (f_78 hg) (h := ?_)
  refine nx pl.base 536 540 (h := ?_)
  refine reach_gen fun v78 e78 => ?_
  refine r_umulh hrun (f_7c hg) (h := ?_)
  refine nx pl.base 540 544 (h := ?_)
  refine reach_gen fun v7c e7c => ?_
  refine r_extr hrun (f_80 hg) (h := ?_)
  refine nx pl.base 544 548 (h := ?_)
  refine reach_gen fun v80 e80 => ?_
  refine r_umulh hrun (f_84 hg) (h := ?_)
  refine nx pl.base 548 552 (h := ?_)
  refine reach_gen fun v84 e84 => ?_
  refine r_adds hrun (f_88 hg) (h := fun ps88 c88 => ?_)
  refine nx pl.base 552 556 (h := ?_)
  refine reach_gen fun v88 e88 => ?_
  refine r_mul hrun (f_8c hg) (h := ?_)
  refine nx pl.base 556 560 (h := ?_)
  refine reach_gen fun v8c e8c => ?_
  refine r_adc hrun (f_90 hg) (h := ?_)
  refine nx pl.base 560 564 (h := ?_)
  refine reach_gen fun v90 e90 => ?_
  refine r_mul hrun (f_94 hg) (h := ?_)
  refine nx pl.base 564 568 (h := ?_)
  refine reach_gen fun v94 e94 => ?_
  refine r_umulh hrun (f_98 hg) (h := ?_)
  refine nx pl.base 568 572 (h := ?_)
  refine reach_gen fun v98 e98 => ?_
  refine r_umulh hrun (f_9c hg) (h := ?_)
  refine nx pl.base 572 576 (h := ?_)
  refine reach_gen fun v9c e9c => ?_
  refine r_adds hrun (f_a0 hg) (h := fun psa0 ca0 => ?_)
  refine nx pl.base 576 580 (h := ?_)
  refine reach_gen fun va0 ea0 => ?_
  refine r_andMask 44 hrun (f_a4 hg) (h := ?_)
  refine nx pl.base 580 584 (h := ?_)
  refine reach_gen fun va4 ea4 => ?_
  refine r_mul hrun (f_a8 hg) (h := ?_)
  refine nx pl.base 584 588 (h := ?_)
  refine reach_gen fun va8 ea8 => ?_
  refine r_adc hrun (f_ac hg) (h := ?_)
  refine nx pl.base 588 592 (h := ?_)
  refine reach_gen fun vac eac => ?_
  refine r_umulh hrun (f_b0 hg) (h := ?_)
  refine nx pl.base 592 596 (h := ?_)
  refine reach_gen fun vb0 eb0 => ?_
  refine r_adds hrun (f_b4 hg) (h := fun psb4 cb4 => ?_)
  refine nx pl.base 596 600 (h := ?_)
  refine reach_gen fun vb4 eb4 => ?_
  refine r_cinc hrun (f_b8 hg) (h := ?_)
  refine nx pl.base 600 604 (h := ?_)
  refine reach_gen fun vb8 eb8 => ?_
  refine r_adds hrun (f_bc hg) (h := fun psbc cbc => ?_)
  refine nx pl.base 604 608 (h := ?_)
  refine reach_gen fun vbc ebc => ?_
  refine r_adc hrun (f_c0 hg) (h := ?_)
  refine nx pl.base 608 612 (h := ?_)
  refine reach_gen fun vc0 ec0 => ?_
  refine r_andMask 44 hrun (f_c4 hg) (h := ?_)
  refine nx pl.base 612 616 (h := ?_)
  refine reach_gen fun vc4 ec4 => ?_
  refine r_extr hrun (f_c8 hg) (h := ?_)
  refine nx pl.base 616 620 (h := ?_)
  refine reach_gen fun vc8 ec8 => ?_
  refine r_mul hrun (f_cc hg) (h := ?_)
  refine nx pl.base 620 624 (h := ?_)
  refine reach_gen fun vcc ecc => ?_
  refine r_umulh hrun (f_d0 hg) (h := ?_)
  refine nx pl.base 624 628 (h := ?_)
  refine reach_gen fun vd0 ed0 => ?_
  refine r_adds hrun (f_d4 hg) (h := fun psd4 cd4 => ?_)
  refine nx pl.base 628 632 (h := ?_)
  refine reach_gen fun vd4 ed4 => ?_
  refine r_cinc hrun (f_d8 hg) (h := ?_)
  refine nx pl.base 632 636 (h := ?_)
  refine reach_gen fun vd8 ed8 => ?_
  refine r_adds hrun (f_dc hg) (h := fun psdc cdc => ?_)
  refine nx pl.base 636 640 (h := ?_)
  refine reach_gen fun vdc edc => ?_
  refine r_adc hrun (f_e0 hg) (h := ?_)
  refine nx pl.base 640 644 (h := ?_)
  refine reach_gen fun ve0 ee0 => ?_
  refine r_andMask 42 hrun (f_e4 hg) (h := ?_)
  refine nx pl.base 644 648 (h := ?_)
  refine reach_gen fun ve4 ee4 => ?_
  refine r_extr hrun (f_e8 hg) (h := ?_)
  refine nx pl.base 648 652 (h := ?_)
  refine reach_gen fun ve8 ee8 => ?_
  refine r_addLsl hrun (f_ec hg) (h := ?_)
  refine nx pl.base 652 656 (h := ?_)
  refine reach_gen fun vec eec => ?_
  refine r_addLsl hrun (f_f0 hg) (h := ?_)
  refine nx pl.base 656 660 (h := ?_)
  refine reach_gen fun vf0 ef0 => ?_
  refine r_andMask 44 hrun (f_f4 hg) (h := ?_)
  refine nx pl.base 660 664 (h := ?_)
  refine reach_gen fun vf4 ef4 => ?_
  refine r_addLsr hrun (f_f8 hg) (h := ?_)
  refine nx pl.base 664 668 (h := ?_)
  refine reach_gen fun vf8 ef8 => ?_

  simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceEqDiff,
    reduceIte, Nat.mul_one, Nat.reduceSub] at e2c e30 e34 e38 e3c e40 e44 e48 e4c e50 e54 e58 e5c e60 e64 e68 e6c e70 e74 e78 e7c e80 e84 e88 e8c e90 e94 e98 e9c ea0 ea4 ea8 eac eb0 eb4 eb8 ebc ec0 ec4 ec8 ecc ed0 ed4 ed8 edc ee0 ee4 ee8 eec ef0 ef4 ef8
  -- the inputs
  subst hx1; rw [← e2c] at k
  have iT0 := (m.read64 (r 1)).isLt
  have iT1 := v2c.isLt
  rw [h7] at e48; rw [h3] at e44; rw [h15] at e40; rw [h13] at e3c
  rw [h8] at e58 e64 e70 e7c ecc ed0; rw [h9] at e78 e84 e94 e9c; rw [h12] at e8c e98
  rw [h11] at e4c e54; rw [h10] at e50 e60 ea8 eb0
  have t30 := toNat_eq_of e30; have t34 := toNat_eq_of e34; have t38 := toNat_eq_of e38
  have t3c := toNat_eq_of e3c; have t40 := toNat_eq_of e40; have t44 := toNat_eq_of e44
  have t48 := toNat_eq_of e48
  -- the limbs of h + block + hibit
  have qA0 : v48.toNat = la0 H0 (m.read64 (r 1)).toNat := by
    unfold la0; clear * - t30 t48 iT0 bH0; omega
  have qA1 : v44.toNat = la1 H1 (m.read64 (r 1)).toNat v2c.toNat := by
    unfold la1; clear * - t34 t38 t44 iT0 iT1 bH1
    have : (m.read64 (r 1)).toNat / 17592186044416 < 2 ^ 20 := by omega
    omega
  have qA2 : v40.toNat = la2 H2 (HF * 2 ^ 40) v2c.toNat := by
    unfold la2; clear * - t3c t40 iT1 bH2 bHF; omega
  have bA0 : la0 H0 (m.read64 (r 1)).toNat < 2 ^ 45 := by unfold la0; clear * - bH0; omega
  have bA1 : la1 H1 (m.read64 (r 1)).toNat v2c.toNat < 2 ^ 45 + 64 := by
    unfold la1; clear * - bH1; omega
  have bA2 : la2 H2 (HF * 2 ^ 40) v2c.toNat < 2 ^ 42 + 2 ^ 41 := by
    unfold la2; clear * - bH2 bHF iT1; omega
  clear t30 t34 t38 t3c t40 t44 t48 e30 e34 e38 e3c e40 e44 e48
  rw [qA0] at e58 e64 e78 e84 e8c e98; rw [qA1] at e50 e60 e70 e7c e94 e9c
  rw [qA2] at e4c e54 ea8 eb0 ecc ed0
  generalize hA0 : la0 H0 (m.read64 (r 1)).toNat = A0 at *
  generalize hA1 : la1 H1 (m.read64 (r 1)).toNat v2c.toNat = A1 at *
  generalize hA2 : la2 H2 (HF * 2 ^ 40) v2c.toNat = A2 at *
  have cols := blk_cols A0 A1 A2 R0 R1 R2 k0 k1 k2 bA0 bA1 bA2
  have cD := cols
  simp only [D0, D1, D2] at cD
  have a0' : A0 < 2 ^ 46 := by omega
  have a1' : A1 < 2 ^ 46 := by omega
  have a2' : A2 < 2 ^ 46 := by omega
  have r0' : R0 < 2 ^ 50 := by omega
  have r1' : R1 < 2 ^ 50 := by omega
  have r2' : R2 < 2 ^ 50 := by omega
  have s1' : 20 * R1 < 2 ^ 50 := by omega
  have s2' : 20 * R2 < 2 ^ 50 := by omega
  -- products: lo + 2^64 hi = product
  have p2s1 := mul128 (toNat_eq_of e4c) (toNat_eq_of e54) (mul_lt_128 a2' s1')
  have p1s2 := mul128 (toNat_eq_of e50) (toNat_eq_of e60) (mul_lt_128 a1' s2')
  have p00 := mul128 (toNat_eq_of e58) (toNat_eq_of e64) (mul_lt_128 a0' r0')
  have p10 := mul128 (toNat_eq_of e70) (toNat_eq_of e7c) (mul_lt_128 a1' r0')
  have p01 := mul128 (toNat_eq_of e78) (toNat_eq_of e84) (mul_lt_128 a0' r1')
  have p02 := mul128 (toNat_eq_of e8c) (toNat_eq_of e98) (mul_lt_128 a0' r2')
  have p11 := mul128 (toNat_eq_of e94) (toNat_eq_of e9c) (mul_lt_128 a1' r1')
  have p2s2 := mul128 (toNat_eq_of ea8) (toNat_eq_of eb0) (mul_lt_128 a2' s2')
  have p20 := mul128 (toNat_eq_of ecc) (toNat_eq_of ed0) (mul_lt_128 a2' r0')
  clear e4c e54 e50 e60 e58 e64 e70 e7c e78 e84 e8c e98 e94 e9c ea8 eb0 ecc ed0
  -- column sums
  have d0a := add128 (toNat_eq_of e5c) (toNat_eq_of e68) c5c
    ⟨v50.isLt, v4c.isLt, by clear * - p2s1 p1s2 cD; omega⟩
  have d0 := add128 (toNat_eq_of e6c) (toNat_eq_of e74) c6c
    ⟨v5c.isLt, v58.isLt, by clear * - p2s1 p1s2 p00 cD d0a; omega⟩
  have q1 := add128 (toNat_eq_of e88) (toNat_eq_of e90) c88
    ⟨v78.isLt, v70.isLt, by clear * - p10 p01 cD; omega⟩
  have q2 := add128 (toNat_eq_of ea0) (toNat_eq_of eac) ca0
    ⟨v8c.isLt, v94.isLt, by clear * - p02 p11 cD; omega⟩
  clear e5c e68 e6c e74 e88 e90 ea0 eac
  have hD0 : v6c.toNat + 2 ^ 64 * v74.toNat = D0 A0 A1 A2 R0 R1 R2 := by
    simp only [D0]; clear * - d0 d0a p00 p1s2 p2s1; omega
  have hQ1 : v88.toNat + 2 ^ 64 * v90.toNat = A0 * R1 + A1 * R0 := by
    clear * - q1 p10 p01; omega
  have hQ2 : va0.toNat + 2 ^ 64 * vac.toNat = A0 * R2 + A1 * R1 := by
    clear * - q2 p02 p11; omega
  clear p00 p1s2 p2s1 p01 p10 p02 p11 d0a d0 q1 q2
  -- carries
  have q80 := extr128 (toNat_eq_of e80) (by rw [hD0]; clear * - cols; omega) v6c.isLt
  have e1a := add128c (toNat_eq_of eb4) (toNat_eq_of eb8) cb4
    ⟨v80.isLt, va8.isLt, by clear * - cols hD0 q80 p2s2 cD; omega⟩
  have e1 := add128 (toNat_eq_of ebc) (toNat_eq_of ec0) cbc
    ⟨vb4.isLt, v88.isLt, by clear * - cols hD0 q80 p2s2 cD e1a hQ1; omega⟩
  have hE1 : vbc.toNat + 2 ^ 64 * vc0.toNat = E1 A0 A1 A2 R0 R1 R2 := by
    simp only [E1, D1]; rw [← hD0, ← q80]; clear * - e1 e1a p2s2 hQ1; omega
  have qc8 := extr128 (toNat_eq_of ec8) (by rw [hE1]; simp only [E1]; clear * - cols; omega) vbc.isLt
  have e2a := add128c (toNat_eq_of ed4) (toNat_eq_of ed8) cd4
    ⟨vc8.isLt, vcc.isLt, by clear * - cols hE1 qc8 p20 cD; simp only [E1] at *; omega⟩
  have e2 := add128 (toNat_eq_of edc) (toNat_eq_of ee0) cdc
    ⟨vd4.isLt, va0.isLt, by clear * - cols hE1 qc8 p20 cD e2a hQ2; simp only [E1] at *; omega⟩
  have hE2 : vdc.toNat + 2 ^ 64 * ve0.toNat = E2 A0 A1 A2 R0 R1 R2 := by
    simp only [E2, D2]; rw [← hE1, ← qc8]; clear * - e2 e2a p20 hQ2; omega
  have bE2 : E2 A0 A1 A2 R0 R1 R2 < 2 ^ 102 := by
    simp only [E2, E1]; clear * - cols; omega
  have qe8 := extr128' (toNat_eq_of ee8) (by rw [hE2]; clear * - bE2; omega) vdc.isLt
  have ta4 := toNat_eq_of ea4; have tc4 := toNat_eq_of ec4; have te4 := toNat_eq_of ee4
  have tec := toNat_eq_of eec; have tf0 := toNat_eq_of ef0; have tf4 := toNat_eq_of ef4
  have tf8 := toNat_eq_of ef8
  clear e80 eb4 eb8 ebc ec0 ec8 ed4 ed8 edc ee0 ee8 ea4 ec4 ee4 eec ef0 ef4 ef8
  rw [hE2] at qe8
  have hF : vf0.toNat = F A0 A1 A2 R0 R1 R2 := by
    simp only [F]
    have : va4.toNat = D0 A0 A1 A2 R0 R1 R2 % 2 ^ 44 := by clear * - ta4 hD0; omega
    clear * - this tec tf0 qe8 bE2; omega
  have hN0 : vf4.toNat = N0 A0 A1 A2 R0 R1 R2 := by
    simp only [N0]; clear * - tf4 hF; omega
  have hN1 : vf8.toNat = N1 A0 A1 A2 R0 R1 R2 := by
    simp only [N1]
    have : vc4.toNat = E1 A0 A1 A2 R0 R1 R2 % 2 ^ 44 := by clear * - tc4 hE1; omega
    have bF : F A0 A1 A2 R0 R1 R2 < 2 ^ 64 := by
      simp only [F]; clear * - bE2; omega
    clear * - this tf8 hF bF; omega
  have hN2 : ve4.toNat = N2 A0 A1 A2 R0 R1 R2 := by
    simp only [N2]; clear * - te4 hE2; omega
  simp only [Nat.reducePow] at hA2
  refine k _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [upd, Nat.reduceEqDiff, reduceIte, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  all_goals first | (rw [hA0, hA1, hA2]; first | exact hN0 | exact hN1 | exact hN2) | rfl

end Poly1305Debian.BlocksV2

end
end

section
section
/-! # 64-bit words over byte writes; addresses of the state -/

set_option autoImplicit false

namespace Poly1305Debian.BlocksV2

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

theorem pc_add' (b : BitVec 64) (x y : Nat) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y = b + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem write64_eq (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    m.write64 a v = (((((((m.write8 (a + BitVec.ofNat 64 0) (v.extractLsb' 0 8)).write8
      (a + BitVec.ofNat 64 1) (v.extractLsb' 8 8)).write8 (a + BitVec.ofNat 64 2) (v.extractLsb' 16 8)).write8
      (a + BitVec.ofNat 64 3) (v.extractLsb' 24 8)).write8 (a + BitVec.ofNat 64 4) (v.extractLsb' 32 8)).write8
      (a + BitVec.ofNat 64 5) (v.extractLsb' 40 8)).write8 (a + BitVec.ofNat 64 6) (v.extractLsb' 48 8)).write8
      (a + BitVec.ofNat 64 7) (v.extractLsb' 56 8) := rfl

theorem concat_bytes64 (v : BitVec 64) :
    v.extractLsb' 56 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 40 8 ++ v.extractLsb' 32 8 ++
      v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

theorem read64_eq (m : Memory) (a : BitVec 64) :
    m.read64 a = m.read8 (a + BitVec.ofNat 64 7) ++ m.read8 (a + BitVec.ofNat 64 6) ++
      m.read8 (a + BitVec.ofNat 64 5) ++ m.read8 (a + BitVec.ofNat 64 4) ++
      m.read8 (a + BitVec.ofNat 64 3) ++ m.read8 (a + BitVec.ofNat 64 2) ++
      m.read8 (a + BitVec.ofNat 64 1) ++ m.read8 (a + BitVec.ofNat 64 0) := by
  rfl

theorem read64_congr {m m' : Memory} {a : BitVec 64}
    (h : ∀ k < 8, m.read8 (a + BitVec.ofNat 64 k) = m'.read8 (a + BitVec.ofNat 64 k)) :
    m.read64 a = m'.read64 a := by
  rw [read64_eq, read64_eq, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

theorem read8_write64_ne (m : Memory) (a b : BitVec 64) (v : BitVec 64)
    (h : ∀ k < 8, b ≠ a + BitVec.ofNat 64 k) : (m.write64 a v).read8 b = m.read8 b := by
  rw [write64_eq]
  simp only [read8_write8, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), if_false]

theorem read64_write64_same (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    (m.write64 a v).read64 a = v := by
  rw [write64_eq, read64_eq]
  simp (disch := decide) only [read8_write8, add_ofNat_inj, Nat.reduceEqDiff, ite_true, ite_false]
  exact concat_bytes64 v

/-- Two doublewords at offsets `x`, `y` of one base that do not overlap. -/
theorem read64_write64_ne (m : Memory) (a : BitVec 64) (x y : Nat) (v : BitVec 64)
    (hx : x + 8 ≤ 2 ^ 32) (hy : y + 8 ≤ 2 ^ 32) (hd : x + 8 ≤ y ∨ y + 8 ≤ x) :
    (m.write64 (a + BitVec.ofNat 64 x) v).read64 (a + BitVec.ofNat 64 y) =
      m.read64 (a + BitVec.ofNat 64 y) := by
  apply read64_congr
  intro k hk
  apply read8_write64_ne
  intro j hj e
  rw [pc_add', pc_add', add_ofNat_inj a (by omega) (by omega)] at e
  omega

theorem good_write64 {pl : Placement} {X : String → Option (State → State)} {s0 : State}
    {m : Memory} (hg : Good pl X s0 m) {a : BitVec 64} (ha : ∀ k < 8, W s0 (a + BitVec.ofNat 64 k))
    (v : BitVec 64) : Good pl X s0 (m.write64 a v) := by
  rw [write64_eq]
  exact Good.write8 (Good.write8 (Good.write8 (Good.write8 (Good.write8 (Good.write8
    (Good.write8 (Good.write8 hg (ha 0 (by decide)) _) (ha 1 (by decide)) _) (ha 2 (by decide)) _)
    (ha 3 (by decide)) _) (ha 4 (by decide)) _) (ha 5 (by decide)) _) (ha 6 (by decide)) _)
    (ha 7 (by decide)) _

end Poly1305Debian.BlocksV2

end
end

section
section
/-! # Byte lists: the block loop's specification `blocksAcc`, little-endian words -/

set_option autoImplicit false

namespace Poly1305Debian.BlocksV2

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)

open Arm64 Poly1305Boringssl

theorem foldl_range_congr {α : Type} (f g : α → Nat → α) :
    ∀ (n : Nat) (a : α), (∀ i, i < n → ∀ b, f b i = g b i) →
      (List.range n).foldl f a = (List.range n).foldl g a
  | 0, _, _ => rfl
  | n + 1, a, h => by
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      foldl_range_congr f g n a (fun i hi b => h i (by omega) b)]
    simp [h n (by omega)]

theorem leBytesToNum_append (l1 l2 : List (BitVec 8)) :
    leBytesToNum (l1 ++ l2) = leBytesToNum l1 + 256 ^ l1.length * leBytesToNum l2 := by
  induction l1 with
  | nil => simp [leBytesToNum]
  | cons b l ih =>
    simp only [leBytesToNum, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, List.length_cons, Nat.pow_succ]
    ring

theorem app_toNat {n k : Nat} (x : BitVec n) (y : BitVec k) :
    (x ++ y).toNat = 2 ^ k * x.toNat + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]
  rw [Nat.mul_comm]

/-- A 16-byte block is two 8-byte words. -/
theorem le16_split (L : List (BitVec 8)) (o : Nat) (h : o + 16 ≤ L.length) :
    leBytesToNum ((L.drop o).take 16) =
      leBytesToNum ((L.drop o).take 8) + 2 ^ 64 * leBytesToNum ((L.drop (o + 8)).take 8) := by
  rw [show (16 : Nat) = 8 + 8 from rfl, List.take_add, leBytesToNum_append, List.drop_drop]
  have : ((L.drop o).take 8).length = 8 := by simp; omega
  rw [this]
  norm_num

/-- A doubleword of memory whose bytes are `L[o..o+8)`. -/
theorem read64_toNat_eq {m : Memory} {A : BitVec 64} {L : List (BitVec 8)} {o : Nat}
    (hl : o + 8 ≤ L.length)
    (h : ∀ k (hk : k < 8), m.read8 (A + BitVec.ofNat 64 k) = L[o + k]'(by omega)) :
    (m.read64 A).toNat = leBytesToNum ((L.drop o).take 8) := by
  have e : ∀ k (hk : k < 8), (L.drop o)[k]'(by simp; omega) = m.read8 (A + BitVec.ofNat 64 k) := by
    intro k hk; rw [h k hk]; simp
  have hd : (L.drop o).take 8 = [m.read8 (A + 0#64), m.read8 (A + 1#64), m.read8 (A + 2#64),
      m.read8 (A + 3#64), m.read8 (A + 4#64), m.read8 (A + 5#64), m.read8 (A + 6#64),
      m.read8 (A + 7#64)] := by
    apply List.ext_getElem
    · simp; omega
    · intro k h1 h2
      simp only [List.length_take, List.length_drop] at h1
      rw [List.getElem_take]
      have hk : k < 8 := by omega
      rw [e k hk]
      interval_cases k <;> rfl
  rw [hd]
  simp only [Memory.read64, app_toNat, leBytesToNum, List.foldr_cons, List.foldr_nil]
  omega

/-- The list of the bytes of memory at `A, A+1, …`: its words are the memory's words. -/
theorem u64At_map_read8 (m : Memory) (A : BitVec 64) (n o : Nat) (h : o + 8 ≤ n) :
    u64At ((List.range n).map fun j => m.read8 (A + BitVec.ofNat 64 j)) o =
      (m.read64 (A + BitVec.ofNat 64 o)).toNat := by
  rw [read64_toNat_eq (L := (List.range n).map fun j => m.read8 (A + BitVec.ofNat 64 j)) (o := o)
    (by simp; omega)]
  · rfl
  · intro k hk
    simp [BitVec.ofNat_add, BitVec.add_assoc]

/-- `u64At` reads only bytes `o..o+8`. -/
theorem u64At_take (L : List (BitVec 8)) (n o : Nat) (h : o + 8 ≤ n) :
    u64At (L.take n) o = u64At L o := by
  unfold u64At
  rw [List.drop_take, List.take_take]
  congr 2
  omega

/-- Peel the first block. -/
theorem blocksAcc_drop (r hb a : Nat) (L : List (BitVec 8)) (h : 16 ≤ L.length) :
    blocksAcc r hb a L =
      blocksAcc r hb (r * (a + leBytesToNum (L.take 16) + hb) % p1305) (L.drop 16) := by
  unfold blocksAcc
  rw [List.length_drop, show L.length / 16 = (L.length - 16) / 16 + 1 by omega,
    List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  simp only [Nat.mul_zero, List.drop_zero]
  apply foldl_range_congr
  intro i _ b
  simp only [List.drop_drop]
  rw [show 16 * i.succ = 16 + 16 * i by omega]

/-- No complete block. -/
theorem blocksAcc_short (r hb a : Nat) (L : List (BitVec 8)) (h : L.length < 16) :
    blocksAcc r hb a L = a := by
  unfold blocksAcc
  rw [show L.length / 16 = 0 by omega]
  rfl

/-- Only the accumulator modulo `p` matters. -/
theorem blocksAcc_mod (r hb a a' : Nat) (L : List (BitVec 8)) (h : a % p1305 = a' % p1305) :
    blocksAcc r hb a L % p1305 = blocksAcc r hb a' L % p1305 := by
  rcases Nat.lt_or_ge L.length 16 with hl | hl
  · rw [blocksAcc_short _ _ _ _ hl, blocksAcc_short _ _ _ _ hl, h]
  · rw [blocksAcc_drop _ _ _ _ hl, blocksAcc_drop _ _ _ _ hl]
    have e : r * (a + leBytesToNum (L.take 16) + hb) % p1305 =
        r * (a' + leBytesToNum (L.take 16) + hb) % p1305 := by
      have h1 : (a + leBytesToNum (L.take 16)) % p1305 = (a' + leBytesToNum (L.take 16)) % p1305 := by
        rw [Nat.add_mod, h, ← Nat.add_mod]
      have h2 : (a + leBytesToNum (L.take 16) + hb) % p1305 =
          (a' + leBytesToNum (L.take 16) + hb) % p1305 := by
        rw [Nat.add_mod, h1, ← Nat.add_mod]
      rw [Nat.mul_mod, h2, ← Nat.mul_mod]
    rw [e]

end Poly1305Debian.BlocksV2

end
end

section
section
/-! # The entry facts and the prologue of `poly1305_blocks` (function offsets 0x00..0x28) -/

set_option autoImplicit false

namespace Poly1305Debian.BlocksV2

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

theorem reach_of_eq {pl : Placement} {X : String → Option (State → State)} {Q : State → Prop}
    {s s' : State} (e : s' = s) (h : Reach pl X Q s') : Reach pl X Q s := e ▸ h

/-- The hibit flag the code computes (`cset x13, eq` after `cmp w3, #0`). -/
def HFl (fin : BitVec 8) : Nat := if fin = 0#8 then 1 else 0

theorem HFl_le (fin : BitVec 8) : HFl fin ≤ 1 := by
  unfold HFl; split <;> omega

theorem hibit_eq (fin : BitVec 8) : 2 ^ 88 * (HFl fin * 2 ^ 40) = hibit fin := by
  unfold HFl hibit; split <;> simp

/-- What the precondition gives about the entry state. -/
structure Facts (pl : Placement) (X : String → Option (State → State)) (s0 : State)
    (rh : List (BitVec 8)) (fin : BitVec 8) : Prop where
  good : Good pl X s0 s0.mem
  rs : ∀ k < 24, ¬ W s0 (X0 s0 + BitVec.ofNat 64 k) ∧
    (s0.mem.perm (X0 s0 + BitVec.ofNat 64 k)).r = true ∧
    s0.mem.isLazyFree (X0 s0 + BitVec.ofNat 64 k) = false
  fn : ¬ W s0 (X0 s0 + BitVec.ofNat 64 88) ∧ (s0.mem.perm (X0 s0 + BitVec.ofNat 64 88)).r = true ∧
    s0.mem.isLazyFree (X0 s0 + BitVec.ofNat 64 88) = false
  finv : s0.mem.read8 (X0 s0 + BitVec.ofNat 64 88) = fin
  rhl : rh.length = 48
  rhv : ∀ k (hk : k < rh.length), s0.mem.read8 (X0 s0 + BitVec.ofNat 64 k) = rh[k]
  st : StateOk rh

section helpers
variable {s0 : State} {m : Memory}

theorem h_canWrite (hm : MemOk s0 m) (off : Nat) (h1 : 24 ≤ off) (h2 : off + 8 ≤ 48) :
    m.canWrite (X0 s0 + BitVec.ofNat 64 off) 8 = true :=
  canWrite_of hm fun k hk => by rw [pc_add]; exact W_h s0 _ (by omega) (by omega)

theorem h_canRead (hm : MemOk s0 m) (off : Nat) (h1 : 24 ≤ off) (h2 : off + 8 ≤ 48) :
    m.canRead (X0 s0 + BitVec.ofNat 64 off) 8 = true :=
  canRead_W hm fun k hk => by rw [pc_add]; exact W_h s0 _ (by omega) (by omega)

theorem rs_canRead {pl : Placement} {X : String → Option (State → State)} {rh : List (BitVec 8)}
    {fin : BitVec 8} (F : Facts pl X s0 rh fin) (hm : MemOk s0 m) (off : Nat) (h : off + 8 ≤ 24) :
    m.canRead (X0 s0 + BitVec.ofNat 64 off) 8 = true :=
  canRead_notW hm fun k hk => by rw [pc_add]; exact F.rs (off + k) (by omega)

theorem add8 (a : BitVec 64) (x : Nat) : a + BitVec.ofNat 64 x + 8#64 = a + BitVec.ofNat 64 (x + 8) :=
  pc_add a x 8

theorem good_h {pl : Placement} {X : String → Option (State → State)} (hg : Good pl X s0 m)
    (off : Nat) (h1 : 24 ≤ off) (h2 : off + 8 ≤ 48) (v : BitVec 64) :
    Good pl X s0 (m.write64 (X0 s0 + BitVec.ofNat 64 off) v) :=
  good_write64 hg (fun k hk => by rw [pc_add]; exact W_h s0 _ (by omega) (by omega)) v

/-- A word of `r` (offsets `< 24`): that of the entry memory. -/
theorem rs_val {pl : Placement} {X : String → Option (State → State)} {rh : List (BitVec 8)}
    {fin : BitVec 8} (F : Facts pl X s0 rh fin) (hm : MemOk s0 m) (off : Nat) (h : off + 8 ≤ 24) :
    (m.read64 (X0 s0 + BitVec.ofNat 64 off)).toNat = u64At rh off := by
  rw [read64_congr (m' := s0.mem) (fun k hk => by
    rw [pc_add]; exact read8_of_notW hm (F.rs _ (by omega)).1)]
  exact read64_toNat_eq (by rw [F.rhl]; omega) (fun k hk => by rw [pc_add]; exact F.rhv _ _)

/-- A word of `h` in the entry memory. -/
theorem h_val0 {pl : Placement} {X : String → Option (State → State)} {rh : List (BitVec 8)}
    {fin : BitVec 8} (F : Facts pl X s0 rh fin) (off : Nat) (h2 : off + 8 ≤ 48) :
    (s0.mem.read64 (X0 s0 + BitVec.ofNat 64 off)).toNat = u64At rh off :=
  read64_toNat_eq (by rw [F.rhl]; omega) (fun k hk => by rw [pc_add]; exact F.rhv _ _)

theorem fin_canRead {pl : Placement} {X : String → Option (State → State)} {rh : List (BitVec 8)}
    {fin : BitVec 8} (F : Facts pl X s0 rh fin) (hm : MemOk s0 m) :
    m.canRead (X0 s0 + BitVec.ofNat 64 88) 1 = true :=
  canRead_notW hm fun k hk => by
    have : k = 0 := by omega
    subst this; simpa using F.fn

end helpers

variable {pl : Placement} {X : String → Option (State → State)} {Q : State → Prop} {s0 : State}

set_option maxHeartbeats 1000000 in
theorem prologue {rh : List (BitVec 8)} {fin : BitVec 8} (hrun : s0.status = .Running)
    (hpc : s0.pc = pl.base + 416#64) (F : Facts pl X s0 rh fin)
    (k : ∀ (r : Nat → BitVec 64) (ps : PState),
      r 1 = r0 s0 1 → r 2 = r0 s0 1 + r0 s0 2 →
      (r 7).toNat = hLimb rh 0 → (r 3).toNat = hLimb rh 1 → (r 15).toNat = hLimb rh 2 →
      (r 8).toNat = rLimb rh 0 → (r 9).toNat = rLimb rh 1 → (r 12).toNat = rLimb rh 2 →
      (r 11).toNat = 20 * rLimb rh 1 → (r 10).toNat = 20 * rLimb rh 2 → (r 13).toNat = HFl fin →
      Reach pl X Q (mkS s0 (pl.base + 460#64) s0.sp s0.mem ps r)) :
    Reach pl X Q s0 := by
  have hg := F.good
  refine reach_of_eq (show mkS s0 (pl.base + 416#64) s0.sp s0.mem s0.pstate (r0 s0) = s0 by
    rw [← hpc]; exact mkS_self s0) ?_
  refine r_ldp64 hrun (f_0 hg) (a := X0 s0 + BitVec.ofNat 64 16) (ha := rfl)
    (hr1 := rs_canRead F hg.2.2 16 (by decide))
    (hr2 := by rw [add8]; exact h_canRead hg.2.2 24 (by decide) (by decide)) (h := ?_)
  rw [add8]
  refine nx pl.base 416 420 (h := ?_)
  refine r_addLsl hrun (f_4 hg) (h := ?_)
  refine nx pl.base 420 424 (h := ?_)
  refine r_ldp64 hrun (f_8 hg) (a := X0 s0 + BitVec.ofNat 64 0) (ha := rfl)
    (hr1 := rs_canRead F hg.2.2 0 (by decide))
    (hr2 := by rw [add8]; exact rs_canRead F hg.2.2 8 (by decide)) (h := ?_)
  rw [add8]
  refine nx pl.base 424 428 (h := ?_)
  refine r_ldrb hrun (f_c hg) (a := X0 s0 + BitVec.ofNat 64 88) (ha := rfl)
    (hr := fin_canRead F hg.2.2) (h := ?_)
  refine nx pl.base 428 432 (h := ?_)
  refine r_cmpW0 hrun (f_10 hg) (h := fun ps10 z10 => ?_)
  refine nx pl.base 432 436 (h := ?_)
  refine r_addLsl hrun (f_14 hg) (h := ?_)
  refine nx pl.base 436 440 (h := ?_)
  refine r_ldp64 hrun (f_18 hg) (a := X0 s0 + BitVec.ofNat 64 32) (ha := rfl)
    (hr1 := h_canRead hg.2.2 32 (by decide) (by decide))
    (hr2 := by rw [add8]; exact h_canRead hg.2.2 40 (by decide) (by decide)) (h := ?_)
  rw [add8]
  refine nx pl.base 440 444 (h := ?_)
  refine r_addLsl hrun (f_1c hg) (h := ?_)
  refine nx pl.base 444 448 (h := ?_)
  refine r_cset hrun (f_20 hg) (h := ?_)
  refine nx pl.base 448 452 (h := ?_)
  refine r_lsl2 hrun (f_24 hg) (h := ?_)
  refine nx pl.base 452 456 (h := ?_)
  refine r_lsl2 hrun (f_28 hg) (h := ?_)
  refine nx pl.base 456 460 (h := ?_)
  have e0 := rs_val F hg.2.2 0 (by decide)
  have e8 := rs_val F hg.2.2 8 (by decide)
  have e16 := rs_val F hg.2.2 16 (by decide)
  have h24 := h_val0 F 24 (by decide)
  have h32 := h_val0 F 32 (by decide)
  have h40 := h_val0 F 40 (by decide)
  have hfin := F.finv
  obtain ⟨_, k0, k1, k2, _, _, _⟩ := F.st
  simp only [rLimb, u64At, Nat.reduceMul] at k0 k1 k2
  simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte,
    Nat.reduceAdd] at e0 e8 e16 h24 h32 h40 hfin z10
  refine k _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp only [upd, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff,
    reduceIte, Nat.reduceAdd]
  · apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  · exact h24
  · exact h32
  · exact h40
  · exact e0
  · exact e8
  · exact e16
  · rw [e8]; simp only [rLimb, u64At, Nat.reduceMul] at *; omega
  · rw [e16]; simp only [rLimb, u64At, Nat.reduceMul] at *; omega
  · rw [hfin] at z10
    have hl := fin.isLt
    unfold HFl
    by_cases hf : fin = 0#8
    · subst hf; simp at z10; simp [z10]
    · have : fin.toNat ≠ 0 := fun e => hf (BitVec.eq_of_toNat_eq e)
      have hz : ps10.z = false := by rw [z10]; simp; omega
      simp [hz, hf]

end Poly1305Debian.BlocksV2

end
end

section
section
/-! # The epilogue (function offsets 0x104..0x10c) and the block loop (induction on the
remaining message; loop test `cmp x1, x2; b.ne` at 0xfc..0x100) -/

set_option autoImplicit false

namespace Poly1305Debian.BlocksV2

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)
open Arm64 Arm64.Obj Poly1305Boringssl

/-- Returned (`pc = lr`, `sp` unchanged, registers above `x17` unchanged, memory changed only in
`W`), with accumulator words in `StateOk` range and congruent to `T`. -/
def Fin (s0 : State) (T : Nat) (sf : State) : Prop :=
  ∃ m r ps, sf = mkS s0 (s0.readReg64 (.gpr 0x1e#5)) s0.sp m ps r ∧ MemOk s0 m ∧
    (m.read64 (X0 s0 + BitVec.ofNat 64 24)).toNat < 2 ^ 44 ∧
    (m.read64 (X0 s0 + BitVec.ofNat 64 32)).toNat < 2 ^ 44 + 64 ∧
    (m.read64 (X0 s0 + BitVec.ofNat 64 40)).toNat < 2 ^ 42 ∧
    ((m.read64 (X0 s0 + BitVec.ofNat 64 24)).toNat +
      2 ^ 44 * (m.read64 (X0 s0 + BitVec.ofNat 64 32)).toNat +
      2 ^ 88 * (m.read64 (X0 s0 + BitVec.ofNat 64 40)).toNat) % p1305 = T % p1305

variable {pl : Placement} {X : String → Option (State → State)} {s0 : State}

set_option maxHeartbeats 1000000 in
theorem epilogue (hrun : s0.status = .Running) {m : Memory} {r : Nat → BitVec 64} {ps : PState}
    (hg : Good pl X s0 m) {T : Nat}
    (b7 : (r 7).toNat < 2 ^ 44) (b3 : (r 3).toNat < 2 ^ 44 + 64) (b15 : (r 15).toNat < 2 ^ 42)
    (hv : ((r 7).toNat + 2 ^ 44 * (r 3).toNat + 2 ^ 88 * (r 15).toNat) % p1305 = T % p1305) :
    Reach pl X (Fin s0 T) (mkS s0 (pl.base + 676#64) s0.sp m ps r) := by
  refine r_stp64 hrun (f_104 hg) (a := X0 s0 + BitVec.ofNat 64 24) (ha := rfl)
    (hw1 := h_canWrite hg.2.2 24 (by decide) (by decide))
    (hw2 := by rw [add8]; exact h_canWrite hg.2.2 32 (by decide) (by decide)) (h := ?_)
  rw [add8]
  have hg2 := good_h (good_h hg 24 (by decide) (by decide) (r (0x07#5).toNat)) (24 + 8)
    (by decide) (by decide) (r (0x03#5).toNat)
  refine nx pl.base 676 680 (h := ?_)
  refine r_str64 hrun (f_108 hg2) (a := X0 s0 + BitVec.ofNat 64 40) (ha := rfl)
    (hw := h_canWrite hg2.2.2 40 (by decide) (by decide)) (h := ?_)
  have hg3 := good_h hg2 40 (by decide) (by decide) (r (0x0f#5).toNat)
  refine nx pl.base 680 684 (h := ?_)
  refine r_ret hrun (f_10c hg3) (h := ?_)
  refine reach_done ⟨_, _, _, rfl, hg3.2.2, ?_⟩
  simp (disch := decide) only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd,
    read64_write64_ne, read64_write64_same]
  exact ⟨b7, b3, b15, hv⟩

/-- The message bytes at `X1`: outside `W`, readable at entry. -/
def MsgOk (s0 : State) (X1 : BitVec 64) (n : Nat) : Prop :=
  ∀ j < n, ¬ W s0 (X1 + BitVec.ofNat 64 j) ∧ (s0.mem.perm (X1 + BitVec.ofNat 64 j)).r = true ∧
    s0.mem.isLazyFree (X1 + BitVec.ofNat 64 j) = false

set_option maxHeartbeats 2000000 in
theorem loop {rh : List (BitVec 8)} {fin : BitVec 8} (hrun : s0.status = .Running)
    (F : Facts pl X s0 rh fin) {T : Nat} :
    ∀ d (rest : List (BitVec 8)) (X1 : BitVec 64) (r : Nat → BitVec 64) (ps : PState),
      rest.length ≤ d → 16 ≤ rest.length → rest.length % 16 = 0 → rest.length < 2 ^ 64 →
      MsgOk s0 X1 rest.length →
      (∀ j (hj : j < rest.length), s0.mem.read8 (X1 + BitVec.ofNat 64 j) = rest[j]) →
      (r 7).toNat < 2 ^ 44 → (r 3).toNat < 2 ^ 44 + 64 → (r 15).toNat < 2 ^ 42 →
      blocksAcc (limbVal (rLimb rh)) (hibit fin)
          ((r 7).toNat + 2 ^ 44 * (r 3).toNat + 2 ^ 88 * (r 15).toNat) rest % p1305 = T % p1305 →
      r 1 = X1 → r 2 = X1 + BitVec.ofNat 64 rest.length →
      (r 8).toNat = rLimb rh 0 → (r 9).toNat = rLimb rh 1 → (r 12).toNat = rLimb rh 2 →
      (r 11).toNat = 20 * rLimb rh 1 → (r 10).toNat = 20 * rLimb rh 2 → (r 13).toNat = HFl fin →
      Reach pl X (Fin s0 T) (mkS s0 (pl.base + 460#64) s0.sp s0.mem ps r) := by
  intro d
  induction d with
  | zero => intro rest _ _ _ hl h16; omega
  | succ d ih =>
    intro rest X1 r ps hl h16 h16d h64 hmsg hbytes b7 b3 b15 hT h1 h2 h8 h9 h12 h11 h10 h13
    have hg := F.good
    obtain ⟨_, k0, k1, k2, _, _, _⟩ := F.st
    have hT0 : (s0.mem.read64 X1).toNat = leBytesToNum ((rest.drop 0).take 8) := by
      have := read64_toNat_eq (m := s0.mem) (A := X1) (L := rest) (o := 0) (by omega)
        (fun k hk => by rw [hbytes k (by omega)]; simp)
      exact this
    have hT1 : (s0.mem.read64 (X1 + 8#64)).toNat = leBytesToNum ((rest.drop 8).take 8) :=
      read64_toNat_eq (by omega) (fun k hk => by
        rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, pc_add, hbytes (8 + k) (by omega)])
    have hcr : ∀ o, o + 8 ≤ 16 → s0.mem.canRead (X1 + BitVec.ofNat 64 o) 8 = true := fun o ho =>
      canRead_notW hg.2.2 fun k hk => by rw [pc_add]; exact hmsg _ (by omega)
    refine bodySeg hrun hg h1 (by rw [h1]; simpa using hcr 0 (by decide))
      (by rw [h1]; exact hcr 8 (by decide)) rfl rfl rfl h13 h8 h9 h12 h11 h10 b7 b3 b15
      (HFl_le fin) k0 k1 k2 (fun r' ps' hp => ?_)
    obtain ⟨e1, e2, e8, e9, e10, e11, e12, e13, e7, e3, e15⟩ := hp
    have iT0 := (s0.mem.read64 X1).isLt
    have iT1 := (s0.mem.read64 (X1 + 8#64)).isLt
    have hHF := HFl_le fin
    have bA0 : la0 (r 7).toNat (s0.mem.read64 X1).toNat < 2 ^ 45 := by unfold la0; omega
    have bA1 : la1 (r 3).toNat (s0.mem.read64 X1).toNat (s0.mem.read64 (X1 + 8#64)).toNat <
        2 ^ 45 + 64 := by
      unfold la1; omega
    have bA2 : la2 (r 15).toNat (HFl fin * 2 ^ 40) (s0.mem.read64 (X1 + 8#64)).toNat <
        2 ^ 42 + 2 ^ 41 := by
      unfold la2; omega
    have bnd := blk_bounds _ _ _ _ _ _ k0 k1 k2 bA0 bA1 bA2
    rw [← e7, ← e3, ← e15] at bnd
    obtain ⟨n0, n1, n2⟩ := bnd
    -- the new accumulator: one step of the block loop
    have hblk := le16_split rest 0 (by omega)
    have hmod := blk_mod (la0 (r 7).toNat (s0.mem.read64 X1).toNat)
      (la1 (r 3).toNat (s0.mem.read64 X1).toNat (s0.mem.read64 (X1 + 8#64)).toNat)
      (la2 (r 15).toNat (HFl fin * 2 ^ 40) (s0.mem.read64 (X1 + 8#64)).toNat)
      (rLimb rh 0) (rLimb rh 1) (rLimb rh 2)
    rw [← e7, ← e3, ← e15] at hmod
    have hH := hibit_eq fin
    have hA : la0 (r 7).toNat (s0.mem.read64 X1).toNat +
        2 ^ 44 * la1 (r 3).toNat (s0.mem.read64 X1).toNat (s0.mem.read64 (X1 + 8#64)).toNat +
        2 ^ 88 * la2 (r 15).toNat (HFl fin * 2 ^ 40) (s0.mem.read64 (X1 + 8#64)).toNat =
        (r 7).toNat + 2 ^ 44 * (r 3).toNat + 2 ^ 88 * (r 15).toNat +
          leBytesToNum (rest.take 16) + hibit fin := by
      simp only [List.drop_zero] at hblk hT0
      unfold la0 la1 la2
      rw [hblk, ← hT0, ← hT1, ← hH]
      omega
    rw [hA] at hmod
    have hT' : blocksAcc (limbVal (rLimb rh)) (hibit fin)
        ((r' 7).toNat + 2 ^ 44 * (r' 3).toNat + 2 ^ 88 * (r' 15).toNat) (rest.drop 16) % p1305 =
        T % p1305 := by
      rw [← hT, blocksAcc_drop _ _ _ rest h16]
      apply blocksAcc_mod
      rw [hmod, Nat.mod_mod, Nat.mul_comm]
      rfl
    have hlen : (rest.drop 16).length = rest.length - 16 := by simp
    -- the loop test
    refine r_cmpReg hrun (f_fc hg) (h := fun ps2 z2 => ?_)
    refine nx pl.base 668 672 (h := ?_)
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at z2
    rw [e1, e2, h2] at z2
    have hz : ps2.z = decide (16 = rest.length) := by
      rw [z2, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl]
      exact Bool.decide_congr (add_ofNat_inj X1 (by decide) h64)
    by_cases hmore : 16 ≤ (rest.drop 16).length
    · refine r_bCond_t hrun (f_100 hg) (by
        simp only [ConditionHolds, hz]; simp; omega) ?_
      rw [show pl.base + 672#64 + 0xffffffffffffff2c#64 = pl.base + 460#64 by
        rw [BitVec.add_assoc]; rfl]
      refine ih (rest.drop 16) (X1 + 16#64) r' _ (by simp; omega) hmore (by simp; omega)
        (by omega) ?_ ?_ n0 n1 n2 hT' e1 ?_ (by rw [e8]; exact h8) (by rw [e9]; exact h9)
        (by rw [e12]; exact h12) (by rw [e11]; exact h11) (by rw [e10]; exact h10)
        (by rw [e13]; exact h13)
      · intro j hj
        rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, pc_add]
        exact hmsg _ (by simp at hj; omega)
      · intro j hj
        rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, pc_add, List.getElem_drop]
        exact hbytes (16 + j) (by simp at hj; omega)
      · rw [e2, h2, hlen, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, pc_add]
        congr 2; omega
    · refine r_bCond_f hrun (f_100 hg) (by
        simp only [ConditionHolds, hz]; simp at hmore ⊢; omega) ?_
      refine nx pl.base 672 676 (h := ?_)
      refine epilogue hrun hg n0 n1 n2 ?_
      rw [← hT', blocksAcc_short _ _ _ _ (by omega)]

end Poly1305Debian.BlocksV2

end
end

section
section
/-! # Separation-logic glue: heap cells of the precondition, and `modHeap` for the postcondition

`modHeap h m` is `h` with every read-write byte replaced by the byte of memory `m`. If `h` matched
the entry memory and `m` differs only on read-write bytes of `h` (the region `W`), then
`modHeap h m` matches `m`, and it satisfies the postcondition's assertions. -/

set_option autoImplicit false

namespace Poly1305Debian.BlocksV2

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

end Poly1305Debian.BlocksV2

end
end

section
section
/-! # `poly1305_blocks` meets `blocksSpecV2`: `Poly1305Debian.BlocksV2.goal` -/

set_option autoImplicit false

namespace Poly1305Debian.BlocksV2

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn)
open Arm64 Arm64.Obj Poly1305Boringssl

variable {pl : Placement} {X : String → Option (State → State)} {s0 : State}

/-- The whole function: prologue, then the loop. -/
theorem run {rh : List (BitVec 8)} {fin : BitVec 8} {msg : List (BitVec 8)}
    (hrun : s0.status = .Running) (hpc : s0.pc = pl.base + 416#64) (F : Facts pl X s0 rh fin)
    (hlen : (s0.readReg64 (.gpr 2#5)).toNat = msg.length) (h16 : 16 ≤ msg.length)
    (h16d : msg.length % 16 = 0)
    (hmsg : MsgOk s0 (s0.readReg64 (.gpr 1#5)) msg.length)
    (hbytes : ∀ j (hj : j < msg.length),
      s0.mem.read8 (s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 j) = msg[j]) :
    Reach pl X (Fin s0 (blocksAcc (limbVal (rLimb rh)) (hibit fin) (limbVal (hLimb rh)) msg)) s0 := by
  have h64 : msg.length < 2 ^ 64 := hlen ▸ (s0.readReg64 (.gpr 2#5)).isLt
  obtain ⟨_, _, _, _, b0, b1, b2⟩ := F.st
  refine prologue hrun hpc F (fun r ps h1 h2 e7 e3 e15 e8 e9 e12 e11 e10 e13 => ?_)
  refine loop hrun F msg.length msg _ r ps (Nat.le_refl _) h16 h16d h64 hmsg hbytes
    (by rw [e7]; exact b0) (by rw [e3]; exact b1) (by rw [e15]; exact b2)
    (by rw [e7, e3, e15]; rfl) (h1.trans (r0_eq s0 1)) ?_ e8 e9 e12 e11 e10 e13
  rw [h2, r0_eq s0 1, r0_eq s0 2]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]; exact hlen

theorem fnAddr_blocks (pl : Placement) :
    libsodiumDebianOnetimeauthLib.fnAddr pl "poly1305_blocks [libsodium_la_poly1305_donna]" =
      pl.base + 416#64 :=
  rfl

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

/-- The pure part of the postcondition, for the 48 bytes left at `x0`. -/
theorem post_pure {pl : Placement} {X : String → Option (State → State)} {s0 : State}
    {rh : List (BitVec 8)} {fin : BitVec 8} (F : Facts pl X s0 rh fin) {mF : Memory} {T : Nat}
    (hok : MemOk s0 mF)
    (b0 : (mF.read64 (X0 s0 + BitVec.ofNat 64 24)).toNat < 2 ^ 44)
    (b1 : (mF.read64 (X0 s0 + BitVec.ofNat 64 32)).toNat < 2 ^ 44 + 64)
    (b2 : (mF.read64 (X0 s0 + BitVec.ofNat 64 40)).toNat < 2 ^ 42)
    (hv : ((mF.read64 (X0 s0 + BitVec.ofNat 64 24)).toNat +
      2 ^ 44 * (mF.read64 (X0 s0 + BitVec.ofNat 64 32)).toNat +
      2 ^ 88 * (mF.read64 (X0 s0 + BitVec.ofNat 64 40)).toNat) % p1305 = T % p1305) :
    let st' := (List.range rh.length).map fun j => mF.read8 (X0 s0 + BitVec.ofNat 64 j)
    StateOk st' ∧ st'.take 24 = rh.take 24 ∧ limbVal (hLimb st') % p1305 = T % p1305 := by
  intro st'
  have hl : st'.length = 48 := by simp [st', F.rhl]
  have htake : st'.take 24 = rh.take 24 := by
    apply List.ext_getElem (by simp [hl, F.rhl])
    intro j h1 h2
    have hj : j < 24 := by rw [List.length_take, hl] at h1; omega
    simp only [List.getElem_take, st', List.getElem_map, List.getElem_range]
    rw [read8_of_notW hok (F.rs j hj).1, F.rhv j (by rw [F.rhl]; omega)]
  have hR : ∀ i, i ≤ 2 → rLimb st' i = rLimb rh i := by
    intro i hi
    simp only [rLimb]
    rw [← u64At_take st' 24 (8 * i) (by omega), htake, u64At_take rh 24 (8 * i) (by omega)]
  have hH : ∀ i, i ≤ 2 → hLimb st' i = (mF.read64 (X0 s0 + BitVec.ofNat 64 (24 + 8 * i))).toNat := by
    intro i hi
    simp only [hLimb, st']
    exact u64At_map_read8 mF (X0 s0) rh.length (24 + 8 * i) (by rw [F.rhl]; omega)
  obtain ⟨_, k0, k1, k2, _, _, _⟩ := F.st
  refine ⟨⟨hl, ?_, ?_, ?_, ?_, ?_, ?_⟩, htake, ?_⟩
  · rw [hR 0 (by decide)]; exact k0
  · rw [hR 1 (by decide)]; exact k1
  · rw [hR 2 (by decide)]; exact k2
  · rw [hH 0 (by decide)]; exact b0
  · rw [hH 1 (by decide)]; exact b1
  · rw [hH 2 (by decide)]; exact b2
  · rw [← hv]; simp only [limbVal]
    rw [hH 0 (by decide), hH 1 (by decide), hH 2 (by decide)]

theorem goal :
    internalOk "poly1305_blocks [libsodium_la_poly1305_donna]" (fun _ => blocksSpecV2) := by
  refine ⟨by decide, ?_⟩
  intro pl hP _ X _ _ _ x R s0 hpc hrun hpre _ hCL
  obtain ⟨ro, rh, fin, msg⟩ := x
  change (prog pl X).CodeLoaded s0.mem at hCL
  obtain ⟨H, hH, hm⟩ := hpre
  obtain ⟨h1, h2, hd12, rfl, hpre1, hR⟩ := hH
  obtain ⟨g1, gA, dg, rfl, ⟨rfl, hφ⟩, hrest⟩ := hpre1
  obtain ⟨q1, qB, d1, rfl, hq1, hqB⟩ := hrest
  obtain ⟨qF, q3, dF, rfl, hqF, hq3⟩ := hqB
  obtain ⟨hst, hlen, h16, h16d⟩ := hφ
  have hx0 : s0.readReg64 Reg.x0 = X0 s0 := rfl
  rw [hx0] at hq1 hqF
  set X1 := s0.readReg64 Reg.x1 with hX1
  set hh := Heap.empty.union (q1.union (qF.union q3)) with hhh
  have hl48 : rh.length = 48 := hst.1
  -- cells of the components
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
  -- cells of the whole precondition heap
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
  have F : Facts pl X s0 rh fin := {
    good := ⟨hP, hCL, fun a _ => rfl, fun a w => by
      obtain ⟨b, hb⟩ := wdom a w
      have := hm.1 a _ (cell_union_left hb)
      exact ⟨this.2.1, this.2.2, rfl, this.2.1⟩⟩
    rs := fun k hk => ⟨not_inRegion_h (X0 s0) k (Or.inl hk),
      (mt _ _ (Or.inl (cS k (by omega)))).2.1, (mt _ _ (Or.inl (cS k (by omega)))).2.2⟩
    fn := ⟨not_inRegion_h (X0 s0) 88 (Or.inr ⟨by omega, by omega⟩),
      (mt _ _ (Or.inl cF')).2.1, (mt _ _ (Or.inl cF')).2.2⟩
    finv := (mt _ _ (Or.inl cF')).1
    rhl := hl48
    rhv := fun k hk => (mt _ _ (Or.inl (cS k hk))).1
    st := hst }
  have hmsg : MsgOk s0 X1 msg.length := fun j hj => ⟨by
      intro w
      obtain ⟨e, ht⟩ := inRegion_eq w
      rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, pc_add] at e
      have h := c1 (24 + (X1 + BitVec.ofNat 64 j - (X0 s0 + BitVec.ofNat 64 24)).toNat) (by omega)
      rw [← e] at h
      exact disj_own d1 h (own_right dF (cM j hj)),
    (mt _ _ (cM' j hj)).2.1, (mt _ _ (cM' j hj)).2.2⟩
  have hbytes : ∀ j (hj : j < msg.length), s0.mem.read8 (X1 + BitVec.ofNat 64 j) = msg[j] :=
    fun j hj => (mt _ _ (cM' j hj)).1
  have hreach := run hrun (hpc.trans (fnAddr_blocks pl)) F hlen h16 h16d hmsg hbytes
  obtain ⟨sf, hsteps, mF, rF, psF, rfl, hok, b0, b1, b2, hv⟩ := hreach
  refine ⟨_, hsteps, Or.inl ⟨⟨rfl, rfl, hrun⟩, ⟨rfl, ?_⟩, ?_⟩⟩
  · exact ⟨rd_hi _ _ _ _ _ _ _ (by decide), rd_hi _ _ _ _ _ _ _ (by decide),
      rd_hi _ _ _ _ _ _ _ (by decide), rd_hi _ _ _ _ _ _ _ (by decide),
      rd_hi _ _ _ _ _ _ _ (by decide), rd_hi _ _ _ _ _ _ _ (by decide),
      rd_hi _ _ _ _ _ _ _ (by decide), rd_hi _ _ _ _ _ _ _ (by decide),
      rd_hi _ _ _ _ _ _ _ (by decide), rd_hi _ _ _ _ _ _ _ (by decide),
      rd_hi _ _ _ _ _ _ _ (by decide), rfl⟩
  · have hpure := post_pure F hok b0 b1 b2 hv
    have h2eq := modHeap_frame hd12 hm hok wdom
    have D := modHeap_disjoint hd12 mF
    have D0 := modHeap_disjoint dg mF
    have D1 := modHeap_disjoint d1 mF
    have DF := modHeap_disjoint dF mF
    rw [h2eq, modHeap_union, modHeap_empty] at D
    simp only [modHeap_union, modHeap_empty] at D0
    rw [modHeap_union] at D1
    refine ⟨modHeap (hh.union h2) mF, ?_,
      modHeap_matches hm hok fun a w => by
        obtain ⟨b, hb⟩ := wdom a w; exact ⟨b, cell_union_left hb⟩⟩
    rw [modHeap_union, h2eq, hhh, modHeap_union, modHeap_empty]
    simp only [modHeap_union] at D ⊢
    refine ⟨_, h2, D, rfl, ?_, hR⟩
    refine ⟨Heap.empty, _, D0, rfl, ⟨rfl, rfl, rd_hi _ _ _ _ _ _ _ (by decide)⟩, ?_⟩
    refine ⟨modHeap q1 mF, _, D1, rfl, ?_, modHeap qF mF, _, DF, rfl, ?_, ?_⟩
    · exact ⟨_, modHeap q1 mF, Heap.empty, disjoint_empty _, (union_empty _).symm,
        modHeap_bytes rh _ q1 mF hq1, rfl, hpure⟩
    · have := bytesIn_mod (ro := false) mF (a := X0 s0 + 88#64) (bs := [fin]) hqF (fun k hk => by
        have : k = 0 := by simp at hk; omega
        subst this
        simpa [read8_of_notW hok F.fn.1] using F.finv)
      exact this
    · exact bytesIn_mod mF hq3 (fun k hk => by
        rw [read8_of_notW hok (hmsg k hk).1]; exact hbytes k hk)

end Poly1305Debian.BlocksV2

end
end

section
section
namespace Poly1305Debian

theorem internalOk_poly1305_blocks_specV2 :
    internalOk "poly1305_blocks [libsodium_la_poly1305_donna]" (fun _ => blocksSpecV2) :=
  BlocksV2.goal

end Poly1305Debian

end
end

section
section
/-! Bridge from the local `blocksSpecV2` (one pure conjunct) to the published `blocksWholeSpec`
(`⌜m.length % 16 = 0⌝ ∗ blocksSpec.pre`): the two preconditions differ only in where the pure fact
sits; every other field is `blocksSpec`'s. -/

set_option autoImplicit false

namespace Poly1305Debian.BlocksV2

open Arm64

theorem empty_disjoint (h : Heap) : Heap.empty.Disjoint h := by
  refine ⟨fun _ => Or.inl rfl, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl, ?_, fun _ => Or.inl rfl⟩
  intro _ _ _ _ e
  rcases e with ⟨e, _⟩ | ⟨_, e⟩ <;> cases e

theorem whole_pre_entails (g : Bool × List (BitVec 8) × BitVec 8 × List (BitVec 8)) (s0 : State) :
    blocksWholeSpec.pre g s0 ⊢ blocksSpecV2.pre g s0 := by
  obtain ⟨ro, rh, fin, m⟩ := g
  rintro h ⟨h1, h2, -, rfl, ⟨rfl, ha⟩, h3, h4, -, rfl, ⟨rfl, ⟨hb1, hb2, hb3⟩⟩, hT⟩
  refine ⟨Heap.empty, h4, empty_disjoint _, ?_, ⟨rfl, hb1, hb2, hb3, ha⟩, hT⟩
  simp only [empty_union]

theorem frame_entails {P Q : SepProp} (hPQ : P ⊢ Q) (R : SepProp) : (P ∗ R) ⊢ (Q ∗ R) := by
  rintro h ⟨h1, h2, hd, rfl, hP, hR⟩
  exact ⟨h1, h2, hd, rfl, hPQ _ hP, hR⟩

end Poly1305Debian.BlocksV2

namespace Poly1305Debian

open Arm64

theorem internalOk_poly1305_blocks_v2_dev :
    internalOk "poly1305_blocks [libsodium_la_poly1305_donna]" (fun _ => blocksWholeSpec) := by
  obtain ⟨hmem, hok⟩ := internalOk_poly1305_blocks_specV2
  refine ⟨hmem, fun pl hp hg ex hz hs hl => ?_⟩
  intro x R s0 hpc hst hpre hal
  obtain ⟨h, hh, hm⟩ := hpre
  exact hok pl hp hg ex hz hs hl x R s0 hpc hst
    ⟨h, BlocksV2.frame_entails (BlocksV2.whole_pre_entails x s0) R h hh, hm⟩ hal

end Poly1305Debian

end
end

section
open Poly1305Debian

theorem solution :
    internalOk "poly1305_blocks [libsodium_la_poly1305_donna]" (fun _ => blocksWholeSpec) := by
  apply Poly1305Debian.internalOk_poly1305_blocks_v2_dev <;> assumption

end
