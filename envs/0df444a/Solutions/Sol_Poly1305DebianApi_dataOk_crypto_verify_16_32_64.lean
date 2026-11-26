-- Prove2me | solution 1 for Poly1305DebianApi.dataOk_crypto_verify_16_32_64
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-26T12:22:31.049096+00:00
-- url     : https://prove2.me/submissions/53045dc4-aeb4-43ef-a8a6-6dfe693f4cc7

import Definitions.Def_Poly1305DebianApi_Spec
import Mathlib.Tactic.IntervalCases

section
section
/-! # Instruction fetch for the placed `libsodiumDebianOnetimeauthCt` text block; the state
abstraction for `crypto_verify_n` -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianApi.Verify

open Arm64 Arm64.Obj Poly1305DebianCt

abbrev TXT : CodeBlock := libsodiumDebianOnetimeauthCtText

/-- The placed program the goal talks about, with extern hooks `X`. -/
def prog (pl : Placement) (X : String → Option (State → State)) : Program :=
  libsodiumDebianOnetimeauthCtLib.program pl X

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

theorem code_length : libsodiumDebianOnetimeauthCtPlacedCode.length = 2324 := by decide +kernel

theorem patched_length (pl : Placement) : (TXT.patched pl).length = 2324 := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE]
  show (List.map (fun _ => 4) (List.range (libsodiumDebianOnetimeauthCtPlacedCode.length / 4))).sum = 2324
  rw [code_length]; rfl

theorem hook_none {pl : Placement} (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    (X : String → Option (State → State)) {off : Nat} (hoff : off < 2324) :
    (prog pl X).externAt? (pl.base + BitVec.ofNat 64 off) = none := by
  have hl : TXT.code.length = 2324 := code_length
  have e1 := (hP.text.externs_ok "__stack_chk_fail" (by decide)).2
  have e3 := (hP.text.externs_ok "memset" (by decide)).2
  have e4 := (hP.text.externs_ok "randombytes_buf" (by decide)).2
  have e5 := (hP.text.externs_ok "sodium_memzero" (by decide)).2
  rw [show libsodiumDebianOnetimeauthCtLib.text = TXT from rfl, hl] at e1 e3 e4 e5
  have hpc : (pl.base + BitVec.ofNat 64 off - pl.base).toNat = off := by
    rw [show pl.base + BitVec.ofNat 64 off - pl.base = BitVec.ofNat 64 off by bv_omega,
      BitVec.toNat_ofNat]; omega
  simp only [prog, Program.externAt?, Program.hookAtOff?, PlacedLib.program, hpc]
  rw [show libsodiumDebianOnetimeauthCtLib.text.externs =
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
      (TXT.patchedWord pl off).extractLsb' (8 * k) 8 ∧
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
  have ht := take4_drop_patched (blk := TXT) (pl := pl) hal
    (by rw [show TXT.code = libsodiumDebianOnetimeauthCtPlacedCode from rfl, code_length]; exact hlen)
  have e1 : (prog pl X).code[off + k]'(by omega) =
      (((TXT.patched pl).drop off).take 4)[k]'(by
        simp [List.length_take, List.length_drop, patched_length]; omega) := by
    simp only [List.getElem_take, List.getElem_drop]; rfl
  rw [e1]
  simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * k + i < 32 := by omega
  simp [hi, this]; omega

theorem fetch_word {pl : Placement} {m : Memory} (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {X : String → Option (State → State)} (hCL : (prog pl X).CodeLoaded m) {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 2324) :
    (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 off) = decode (TXT.patchedWord pl off) := by
  have hb4 : pl.base.toNat % 4 = 0 := by
    have := hP.text.base_aligned
    rw [show libsodiumDebianOnetimeauthCtLib.text.align = 32 from rfl] at this
    omega
  have hnw : pl.base.toNat + 2324 ≤ 2 ^ 64 := by
    have := hP.text.no_wrap
    have hl : TXT.code.length = 2324 := code_length
    rw [show libsodiumDebianOnetimeauthCtLib.text = TXT from rfl, hl] at this
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

theorem patchedWord_plain (pl : Placement) {off : Nat} (h : TXT.relocAt? off = none) :
    TXT.patchedWord pl off = TXT.wordAt off := by
  simp [CodeBlock.patchedWord, h]

/-! ## The state abstraction: `x0..x3`, `pc`, `sp`, memory and flags replaced -/

/-- The register file of `s0` with `x0..x3` replaced. -/
def regs4 (rf : RegFile) (x0 x1 x2 x3 : BitVec 64) : RegFile :=
  ⟨fun i => if i = 0#5 then x0 else if i = 1#5 then x1 else if i = 2#5 then x2
    else if i = 3#5 then x3 else rf.regs i⟩

/-- The abstract state. -/
def S (s0 : State) (pc sp : BitVec 64) (m : Memory) (ps : PState) (x0 x1 x2 x3 : BitVec 64) :
    State :=
  { s0 with regs := regs4 s0.regs x0 x1 x2 x3, pc := pc, sp := sp, mem := m, pstate := ps }

section lemmas
variable (s0 : State) (pc sp : BitVec 64) (m : Memory) (ps : PState) (x0 x1 x2 x3 : BitVec 64)

@[simp] theorem S_mem : (S s0 pc sp m ps x0 x1 x2 x3).mem = m := rfl
@[simp] theorem S_pc : (S s0 pc sp m ps x0 x1 x2 x3).pc = pc := rfl
@[simp] theorem S_sp : (S s0 pc sp m ps x0 x1 x2 x3).sp = sp := rfl
@[simp] theorem S_status : (S s0 pc sp m ps x0 x1 x2 x3).status = s0.status := rfl
@[simp] theorem S_pstate : (S s0 pc sp m ps x0 x1 x2 x3).pstate = ps := rfl
@[simp] theorem S_vregs : (S s0 pc sp m ps x0 x1 x2 x3).vregs = s0.vregs := rfl

@[simp] theorem rd0 : (S s0 pc sp m ps x0 x1 x2 x3).readReg64 (.gpr 0#5) = x0 := rfl
@[simp] theorem rd1 : (S s0 pc sp m ps x0 x1 x2 x3).readReg64 (.gpr 1#5) = x1 := rfl
@[simp] theorem rd2 : (S s0 pc sp m ps x0 x1 x2 x3).readReg64 (.gpr 2#5) = x2 := rfl
@[simp] theorem rd3 : (S s0 pc sp m ps x0 x1 x2 x3).readReg64 (.gpr 3#5) = x3 := rfl
@[simp] theorem rd_xzr : (S s0 pc sp m ps x0 x1 x2 x3).readReg64 .xzr = 0#64 := rfl
@[simp] theorem rd_sp : (S s0 pc sp m ps x0 x1 x2 x3).readReg64 .sp = sp := rfl

theorem rd_hi (i : BitVec 5) (h : 3 < i.toNat) :
    (S s0 pc sp m ps x0 x1 x2 x3).readReg64 (.gpr i) = s0.readReg64 (.gpr i) := by
  have h0 : i ≠ 0#5 := by intro e; subst e; simp at h
  have h1 : i ≠ 1#5 := by intro e; subst e; simp at h
  have h2 : i ≠ 2#5 := by intro e; subst e; simp at h
  have h3 : i ≠ 3#5 := by intro e; subst e; simp at h
  simp [S, State.readReg64, regs4, RegFile.read, h0, h1, h2, h3]

@[simp] theorem wr0 (v : BitVec 64) :
    (S s0 pc sp m ps x0 x1 x2 x3).writeReg64 (.gpr 0#5) v = S s0 pc sp m ps v x1 x2 x3 := by
  simp only [S, State.writeReg64, regs4, RegFile.write,
    show (0#5 == 31#5) = false from rfl, Bool.false_eq_true, if_false]
  congr 2; funext j; by_cases hj : j = 0#5 <;> simp [hj]
@[simp] theorem wr1 (v : BitVec 64) :
    (S s0 pc sp m ps x0 x1 x2 x3).writeReg64 (.gpr 1#5) v = S s0 pc sp m ps x0 v x2 x3 := by
  simp only [S, State.writeReg64, regs4, RegFile.write,
    show (1#5 == 31#5) = false from rfl, Bool.false_eq_true, if_false]
  congr 2; funext j; by_cases hj : j = 1#5 <;> simp [hj]
@[simp] theorem wr2 (v : BitVec 64) :
    (S s0 pc sp m ps x0 x1 x2 x3).writeReg64 (.gpr 2#5) v = S s0 pc sp m ps x0 x1 v x3 := by
  simp only [S, State.writeReg64, regs4, RegFile.write,
    show (2#5 == 31#5) = false from rfl, Bool.false_eq_true, if_false]
  congr 2; funext j; by_cases hj : j = 2#5 <;> simp [hj]
@[simp] theorem wr3 (v : BitVec 64) :
    (S s0 pc sp m ps x0 x1 x2 x3).writeReg64 (.gpr 3#5) v = S s0 pc sp m ps x0 x1 x2 v := by
  simp only [S, State.writeReg64, regs4, RegFile.write,
    show (3#5 == 31#5) = false from rfl, Bool.false_eq_true, if_false]
  congr 2; funext j; by_cases hj : j = 3#5 <;> simp [hj]
@[simp] theorem wr_xzr (v : BitVec 64) :
    (S s0 pc sp m ps x0 x1 x2 x3).writeReg64 .xzr v = S s0 pc sp m ps x0 x1 x2 x3 := rfl
@[simp] theorem wr_sp (v : BitVec 64) :
    (S s0 pc sp m ps x0 x1 x2 x3).writeReg64 .sp v = S s0 pc v m ps x0 x1 x2 x3 := rfl
@[simp] theorem S_advancePC :
    (S s0 pc sp m ps x0 x1 x2 x3).advancePC = S s0 (pc + 4#64) sp m ps x0 x1 x2 x3 := rfl
@[simp] theorem S_setPC (q : BitVec 64) :
    (S s0 pc sp m ps x0 x1 x2 x3).setPC q = S s0 q sp m ps x0 x1 x2 x3 := rfl
@[simp] theorem S_setPState (q : PState) :
    (S s0 pc sp m ps x0 x1 x2 x3).setPState q = S s0 pc sp m q x0 x1 x2 x3 := rfl
@[simp] theorem S_setMem (q : Memory) :
    (S s0 pc sp m ps x0 x1 x2 x3).setMem q = S s0 pc sp q ps x0 x1 x2 x3 := rfl
@[simp] theorem S_spAligned :
    (S s0 pc sp m ps x0 x1 x2 x3).spAligned = ((sp &&& 0b1111#64) == 0#64) := rfl

end lemmas

theorem S_self (s0 : State) :
    S s0 s0.pc s0.sp s0.mem s0.pstate (s0.readReg64 (.gpr 0#5)) (s0.readReg64 (.gpr 1#5))
      (s0.readReg64 (.gpr 2#5)) (s0.readReg64 (.gpr 3#5)) = s0 := by
  rcases s0 with ⟨⟨rf⟩⟩
  simp only [S, regs4, State.readReg64, RegFile.read]
  congr 2; funext j
  by_cases h0 : j = 0#5
  · subst h0; simp
  by_cases h1 : j = 1#5
  · subst h1; simp
  by_cases h2 : j = 2#5
  · subst h2; simp
  by_cases h3 : j = 3#5
  · subst h3; simp
  simp [h0, h1, h2, h3]

/-! ## Reachability -/

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

theorem step_S {pl : Placement} {X : String → Option (State → State)} {s0 : State}
    {pc sp : BitVec 64} {m : Memory} {ps : PState} {x0 x1 x2 x3 : BitVec 64} {inst : Instr}
    (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some inst) {s' : State}
    (he : execInstWithSvc (evalSvc Syscall.standard) inst (S s0 pc sp m ps x0 x1 x2 x3) = s') :
    Step (prog pl X) (S s0 pc sp m ps x0 x1 x2 x3) s' := by
  have := Step.exec (prog := prog pl X) (s := S s0 pc sp m ps x0 x1 x2 x3) hrun hf
  rw [Program.evalInst] at this
  rwa [show (prog pl X).svc = Syscall.standard from rfl, he] at this

end Poly1305DebianApi.Verify

end
end

section
section
/-! # Memory: byte writes, the frame `W`, the invariant `MemOk`, and the frame slots

`crypto_verify_n` writes only its 32-byte frame `[sp0 - 32, sp0)` (the region `W`). `MemOk s0 m`:
every cell outside `W` is that of `s0.mem`, and every byte of `W` is mapped read-write (not lazy-free,
anonymity unchanged), as in `s0.mem`. The write8 lemmas follow the accepted
`Solutions/Poly1305DebianBlocks/Mem.lean`. -/

set_option autoImplicit false

namespace Poly1305DebianApi.Verify

open Arm64 Arm64.Obj Poly1305DebianCt

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

/-- The frame base `sp0 - 32`. -/
abbrev B (s0 : State) : BitVec 64 := s0.sp - 32#64

/-- The written region: the 32-byte frame. -/
def W (s0 : State) (a : BitVec 64) : Prop :=
  InRegion (B s0) 32 a

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
  libsodiumDebianOnetimeauthCtLib.Placeable pl ∧ (prog pl X).CodeLoaded s0.mem ∧ MemOk s0 m

theorem Good.codeLoaded {pl : Placement} {X : String → Option (State → State)} {s0 : State}
    {m : Memory} (hg : Good pl X s0 m) : (prog pl X).CodeLoaded m :=
  codeLoaded_of hg.2.1 fun a ha => hg.2.2.1 a fun hw => by
    have := (hg.2.2.2 a hw).2.2.2; rw [ha] at this; cases this

/-! ## The frame: offsets `B + k`, `k < 32` -/

theorem W_off (s0 : State) (k : Nat) (hk : k < 32) : W s0 (B s0 + BitVec.ofNat 64 k) := by
  unfold W InRegion
  rw [show B s0 + BitVec.ofNat 64 k - B s0 = BitVec.ofNat 64 k by bv_omega]
  simp; omega

theorem W_off' (s0 : State) (c k : Nat) (hk : c + k < 32) :
    W s0 (B s0 + BitVec.ofNat 64 c + BitVec.ofNat 64 k) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact W_off s0 _ hk

theorem memOk_write16 {s0 : State} {m : Memory} (hm : MemOk s0 m) (c : Nat) (hc : c + 2 ≤ 32)
    (v : BitVec 16) : MemOk s0 (m.write16 (B s0 + BitVec.ofNat 64 c) v) := by
  simp only [Memory.write16]
  refine memOk_write8 (memOk_write8 hm ?_ _) ?_ _
  · simpa using W_off' s0 c 0 (by omega)
  · exact W_off' s0 c 1 (by omega)

theorem memOk_write64 {s0 : State} {m : Memory} (hm : MemOk s0 m) (c : Nat) (hc : c + 8 ≤ 32)
    (v : BitVec 64) : MemOk s0 (m.write64 (B s0 + BitVec.ofNat 64 c) v) := by
  simp only [Memory.write64]
  refine memOk_write8 (memOk_write8 (memOk_write8 (memOk_write8 (memOk_write8 (memOk_write8
    (memOk_write8 (memOk_write8 hm ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _
  · simpa using W_off' s0 c 0 (by omega)
  · exact W_off' s0 c 1 (by omega)
  · exact W_off' s0 c 2 (by omega)
  · exact W_off' s0 c 3 (by omega)
  · exact W_off' s0 c 4 (by omega)
  · exact W_off' s0 c 5 (by omega)
  · exact W_off' s0 c 6 (by omega)
  · exact W_off' s0 c 7 (by omega)

theorem canWrite_frame {s0 : State} {m : Memory} (hm : MemOk s0 m) (c n : Nat) (hc : c + n ≤ 32) :
    m.canWrite (B s0 + BitVec.ofNat 64 c) n = true :=
  canWrite_of hm fun k hk => W_off' s0 c k (by omega)

theorem canRead_frame {s0 : State} {m : Memory} (hm : MemOk s0 m) (c n : Nat) (hc : c + n ≤ 32) :
    m.canRead (B s0 + BitVec.ofNat 64 c) n = true :=
  canRead_W hm fun k hk => W_off' s0 c k (by omega)

theorem concat_bytes64 (v : BitVec 64) :
    v.extractLsb' 56 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 40 8 ++ v.extractLsb' 32 8 ++
      v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

theorem concat_bytes16 (v : BitVec 16) : v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

/-! ## The three slots: `x` at `B + 16`, `y` at `B + 24`, the accumulator at `B + 14` -/

section slots
variable (s0 : State) (m : Memory)

theorem read16_write16_same (a : BitVec 64) (v : BitVec 16) : (m.write16 a v).read16 a = v := by
  simp [Memory.read16, Memory.write16, read8_write8]
  exact concat_bytes16 v

theorem read64_write64_same (a : BitVec 64) (v : BitVec 64) : (m.write64 a v).read64 a = v := by
  simp [Memory.read64, Memory.write64, read8_write8]
  exact concat_bytes64 v

theorem read64_16_write16_14 (v : BitVec 16) :
    (m.write16 (B s0 + 14#64) v).read64 (B s0 + 16#64) = m.read64 (B s0 + 16#64) := by
  simp [Memory.read64, Memory.write16, read8_write8, BitVec.add_assoc]

theorem read64_24_write16_14 (v : BitVec 16) :
    (m.write16 (B s0 + 14#64) v).read64 (B s0 + 24#64) = m.read64 (B s0 + 24#64) := by
  simp [Memory.read64, Memory.write16, read8_write8, BitVec.add_assoc]

theorem read64_16_write64_24 (v : BitVec 64) :
    (m.write64 (B s0 + 24#64) v).read64 (B s0 + 16#64) = m.read64 (B s0 + 16#64) := by
  simp [Memory.read64, Memory.write64, read8_write8, BitVec.add_assoc]

end slots

/-- The frame facts at a point of the run: `MemOk`, and the three slots. -/
structure Fr (s0 : State) (m : Memory) (x y : BitVec 64) (acc : BitVec 16) : Prop where
  ok : MemOk s0 m
  sx : m.read64 (B s0 + 16#64) = x
  sy : m.read64 (B s0 + 24#64) = y
  sd : m.read16 (B s0 + 14#64) = acc

theorem Fr.write16 {s0 : State} {m : Memory} {x y : BitVec 64} {acc : BitVec 16}
    (F : Fr s0 m x y acc) (v : BitVec 16) : Fr s0 (m.write16 (B s0 + 14#64) v) x y v := by
  refine ⟨memOk_write16 F.ok 14 (by omega) v, ?_, ?_, read16_write16_same _ _ _⟩
  · rw [read64_16_write16_14]; exact F.sx
  · rw [read64_24_write16_14]; exact F.sy

end Poly1305DebianApi.Verify

end
end

section
section
/-! # Separation-logic glue: heap cells of the precondition, and `modHeap` for the postcondition

`modHeap h m` is `h` with every read-write byte replaced by the byte of memory `m`. If `h` matched
the entry memory and `m` differs only on read-write bytes of `h` (the region `W`), then
`modHeap h m` matches `m`, and it satisfies the postcondition's assertions. -/

set_option autoImplicit false

namespace Poly1305DebianApi.Verify

open Poly1305Libsodium (bytesIn)

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

end Poly1305DebianApi.Verify

end
end

section
section
/-! # One reachability lemma per instruction of `crypto_verify_n`

Each `r_*` lemma reduces `Reach` at an abstract state `S …` to `Reach` at its successor. -/

set_option autoImplicit false

namespace Poly1305DebianApi.Verify

open Arm64 Arm64.Obj Poly1305DebianCt

section
variable (svc : State → State) (s : State)
theorem ex_addSubImm (w : RegWidth) (op : AddSubOp) (rd rn : Reg) (imm : BitVec 12) (sh : Bool) :
    execInstWithSvc svc (.addSubImm w op rd rn imm sh) s = execAddSubImm w op rd rn imm sh s := rfl
theorem ex_logicalImm (w : RegWidth) (op : LogicalOp) (rd rn : Reg) (mask : BitVec 64) :
    execInstWithSvc svc (.logicalImm w op rd rn mask) s = execLogicalImm w op rd rn mask s := rfl
theorem ex_logicalShift (w : RegWidth) (op : LogicalOp) (rd rn rm : Reg) (sh : ShiftType) (a : Nat) :
    execInstWithSvc svc (.logicalShift w op rd rn rm sh a) s =
      execLogicalShift w op rd rn rm sh a s := rfl
theorem ex_bitfield (w : RegWidth) (op : BitfieldOp) (rd rn : Reg) (a b : Nat) :
    execInstWithSvc svc (.bitfield w op rd rn a b) s = execBitfield w op rd rn a b s := rfl
theorem ex_moveWide (w : RegWidth) (op : MoveWideOp) (rd : Reg) (imm : BitVec 16) (hw : Nat) :
    execInstWithSvc svc (.moveWide w op rd imm hw) s = execMoveWide w op rd imm hw s := rfl
theorem ex_bCond (c : CondCode) (off : BitVec 64) :
    execInstWithSvc svc (.bCond c off) s =
      if ConditionHolds c s.pstate then s.setPC (s.pc + off) else s.advancePC := rfl
theorem ex_ldr (w : RegWidth) (sz : MemWidth) (sg : Bool) (rt : Reg) (a : AddrMode) :
    execInstWithSvc svc (.ldr w sz sg rt a) s = execLdr w sz sg rt a s := rfl
theorem ex_str (sz : MemWidth) (rt : Reg) (a : AddrMode) :
    execInstWithSvc svc (.str sz rt a) s = execStr sz rt a s := rfl
theorem ex_ret (rn : Reg) : execInstWithSvc svc (.ret rn) s = s.setPC (s.readReg64 rn) := rfl
theorem ex_hint (imm : BitVec 7) : execInstWithSvc svc (.hint imm) s = s.advancePC := rfl
theorem ex_nop : execInstWithSvc svc .nop s = s.advancePC := rfl
theorem ex_adr (page : Bool) (rd : Reg) (off : BitVec 64) :
    execInstWithSvc svc (.adr page rd off) s =
      (s.writeReg64 rd ((if page then s.pc &&& 0xfffffffffffff000#64 else s.pc) + off)).advancePC :=
  rfl
end

variable {pl : Placement} {X : String → Option (State → State)} {Q : State → Prop} {s0 : State}
  {pc sp : BitVec 64} {m : Memory} {ps : PState} {x0 x1 x2 x3 : BitVec 64}

/-- `bti c` / `nop` (hints). -/
theorem r_hint {imm : BitVec 7} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.hint imm))
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps x0 x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) :=
  reach_step (step_S hrun hf (by rw [ex_hint]; rfl)) h

theorem r_nop (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some .nop)
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps x0 x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) :=
  reach_step (step_S hrun hf (by rw [ex_nop]; rfl)) h

/-- `sub sp, sp, #0x20`. -/
theorem r_subSp (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubImm .W64 .SUB .sp .sp 0x020#12 false))
    (h : Reach pl X Q (S s0 (pc + 4#64) (sp - 32#64) m ps x0 x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_addSubImm]
  simp only [execAddSubImm, State.readReg, rd_sp, evalAddSub, State.writeReg, wr_sp, S_advancePC]
  simp [AddWithCarry64, AddWithCarry32]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub]
  omega

/-- `add sp, sp, #0x20`. -/
theorem r_addSp (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubImm .W64 .ADD .sp .sp 0x020#12 false))
    (h : Reach pl X Q (S s0 (pc + 4#64) (sp + 32#64) m ps x0 x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_addSubImm]
  simp only [execAddSubImm, State.readReg, rd_sp, evalAddSub, State.writeReg, wr_sp, S_advancePC]
  simp [AddWithCarry64, AddWithCarry32]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub]
  omega

/-- `str x0, [sp, #0x10]`. -/
theorem r_strX0 (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.str .X64 (.gpr 0#5) (.Offset .sp 0x10#64)))
    (hal : (sp &&& 0b1111#64 == 0#64) = true) (hw : m.canWrite (sp + 0x10#64) 8 = true)
    (h : Reach pl X Q (S s0 (pc + 4#64) sp (m.write64 (sp + 0x10#64) x0) ps x0 x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_str]
  simp only [execStr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, S_spAligned, hal,
    Bool.not_true, Bool.false_eq_true, if_false, evalAddrMode, rd_sp, S_mem, hw, MemWidth.bytes,
    Memory.writeSized, rd0, S_setMem, S_advancePC]

/-- `str x1, [sp, #0x18]`. -/
theorem r_strX1 (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.str .X64 (.gpr 1#5) (.Offset .sp 0x18#64)))
    (hal : (sp &&& 0b1111#64 == 0#64) = true) (hw : m.canWrite (sp + 0x18#64) 8 = true)
    (h : Reach pl X Q (S s0 (pc + 4#64) sp (m.write64 (sp + 0x18#64) x1) ps x0 x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_str]
  simp only [execStr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, S_spAligned, hal,
    Bool.not_true, Bool.false_eq_true, if_false, evalAddrMode, rd_sp, S_mem, hw, MemWidth.bytes,
    Memory.writeSized, rd1, S_setMem, S_advancePC]

/-- `mov x1, #0`. -/
theorem r_movX1 (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.moveWide .W64 .MOVZ (.gpr 1#5) 0x0000#16 0))
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps x0 0#64 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_moveWide]
  simp [execMoveWide, State.writeReg]

/-- `strh wzr, [sp, #0xe]`. -/
theorem r_strhZ (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.str .H16 .xzr (.Offset .sp 0xe#64)))
    (hal : (sp &&& 0b1111#64 == 0#64) = true) (hw : m.canWrite (sp + 0xe#64) 2 = true)
    (h : Reach pl X Q (S s0 (pc + 4#64) sp (m.write16 (sp + 0xe#64) 0#16) ps x0 x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_str]
  simp only [execStr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, S_spAligned, hal,
    Bool.not_true, Bool.false_eq_true, if_false, evalAddrMode, rd_sp, S_mem, hw, MemWidth.bytes,
    Memory.writeSized, rd_xzr, S_setMem, S_advancePC]
  rfl

/-- `strh w0, [sp, #0xe]`. -/
theorem r_strh0 (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.str .H16 (.gpr 0#5) (.Offset .sp 0xe#64)))
    (hal : (sp &&& 0b1111#64 == 0#64) = true) (hw : m.canWrite (sp + 0xe#64) 2 = true)
    (h : Reach pl X Q (S s0 (pc + 4#64) sp (m.write16 (sp + 0xe#64) (x0.setWidth 16)) ps
      x0 x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_str]
  simp only [execStr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, S_spAligned, hal,
    Bool.not_true, Bool.false_eq_true, if_false, evalAddrMode, rd_sp, S_mem, hw, MemWidth.bytes,
    Memory.writeSized, rd0, S_setMem, S_advancePC]

/-- `ldr x0, [sp, #off]`. -/
theorem r_ldrX0 {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ldr .W64 .X64 false (.gpr 0#5) (.Offset .sp off)))
    (hal : (sp &&& 0b1111#64 == 0#64) = true) (hr : m.canRead (sp + off) 8 = true)
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps (m.read64 (sp + off)) x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_ldr]
  simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, S_spAligned, hal,
    Bool.not_true, Bool.false_eq_true, if_false, evalAddrMode, rd_sp, S_mem, hr, MemWidth.bytes,
    Memory.readSized, State.writeReg, wr0, S_advancePC]

/-- `ldrb w3, [x0, x1]`. -/
theorem r_ldrb3 (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ldr .W32 .B8 false (.gpr 3#5)
      (.RegOffset (.gpr 0#5) (.gpr 1#5) .UXTX 0)))
    (hr : m.canRead (x0 + x1) 1 = true)
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps x0 x1 x2 ((m.read8 (x0 + x1)).setWidth 64))) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_ldr]
  have ha : x0 + extendVal .W64 x1 .UXTX 0 = x0 + x1 := by simp [extendVal]
  simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, rd0, rd1, S_mem, ha, hr, MemWidth.bytes,
    Memory.readSized, State.writeReg, wr3, S_advancePC]
  congr 1
  simp

/-- `ldrb w0, [x0, x1]`. -/
theorem r_ldrb0 (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ldr .W32 .B8 false (.gpr 0#5)
      (.RegOffset (.gpr 0#5) (.gpr 1#5) .UXTX 0)))
    (hr : m.canRead (x0 + x1) 1 = true)
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps ((m.read8 (x0 + x1)).setWidth 64) x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_ldr]
  have ha : x0 + extendVal .W64 x1 .UXTX 0 = x0 + x1 := by simp [extendVal]
  simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, rd0, rd1, S_mem, ha, hr, MemWidth.bytes,
    Memory.readSized, State.writeReg, wr0, S_advancePC]
  congr 1
  simp

/-- `add x1, x1, #1`. -/
theorem r_incX1 (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubImm .W64 .ADD (.gpr 1#5) (.gpr 1#5) 0x001#12 false))
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps x0 (x1 + 1#64) x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_addSubImm]
  simp only [execAddSubImm, State.readReg, rd1, evalAddSub, State.writeReg, wr1, S_advancePC]
  simp [AddWithCarry64, AddWithCarry32]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub]
  omega

/-- `ldrh w2, [sp, #0xe]`. -/
theorem r_ldrh2 (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ldr .W32 .H16 false (.gpr 2#5) (.Offset .sp 0xe#64)))
    (hal : (sp &&& 0b1111#64 == 0#64) = true) (hr : m.canRead (sp + 0xe#64) 2 = true)
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps x0 x1 ((m.read16 (sp + 0xe#64)).setWidth 64) x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_ldr]
  simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, S_spAligned, hal,
    Bool.not_true, Bool.false_eq_true, if_false, evalAddrMode, rd_sp, S_mem, hr, MemWidth.bytes,
    Memory.readSized, State.writeReg, wr2, S_advancePC]
  congr 1
  simp

/-- `ldrh w0, [sp, #0xe]`. -/
theorem r_ldrh0 (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ldr .W32 .H16 false (.gpr 0#5) (.Offset .sp 0xe#64)))
    (hal : (sp &&& 0b1111#64 == 0#64) = true) (hr : m.canRead (sp + 0xe#64) 2 = true)
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps ((m.read16 (sp + 0xe#64)).setWidth 64) x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_ldr]
  simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, S_spAligned, hal,
    Bool.not_true, Bool.false_eq_true, if_false, evalAddrMode, rd_sp, S_mem, hr, MemWidth.bytes,
    Memory.readSized, State.writeReg, wr0, S_advancePC]
  congr 1
  simp

/-- `ldrh w1, [x1, #off]`. -/
theorem r_ldrh1 {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ldr .W32 .H16 false (.gpr 1#5) (.Offset (.gpr 1#5) off)))
    (hr : m.canRead (x1 + off) 2 = true)
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps x0 ((m.read16 (x1 + off)).setWidth 64) x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_ldr]
  simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned,
    Bool.not_true, Bool.false_eq_true, if_false, evalAddrMode, rd1, S_mem, hr, MemWidth.bytes,
    Memory.readSized, State.writeReg, wr1, S_advancePC]
  congr 1
  simp

/-- `eor w0, w0, w3`. -/
theorem r_eor03 (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.logicalShift .W32 .EOR (.gpr 0#5) (.gpr 0#5) (.gpr 3#5) .LSL 0))
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps (((x0 ^^^ x3).setWidth 32).setWidth 64) x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_logicalShift]
  simp only [execLogicalShift, State.readReg, State.readReg32, rd0, rd3, evalLogical,
    shiftVal, State.writeReg, wr0, S_advancePC]
  simp [shiftVal, shift32, shift64, evalLogical]

/-- `eor w0, w0, w1`. -/
theorem r_eor01 (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.logicalShift .W32 .EOR (.gpr 0#5) (.gpr 0#5) (.gpr 1#5) .LSL 0))
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps (((x0 ^^^ x1).setWidth 32).setWidth 64) x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_logicalShift]
  simp only [execLogicalShift, State.readReg, State.readReg32, rd0, rd1, evalLogical,
    shiftVal, State.writeReg, wr0, S_advancePC]
  simp [shiftVal, shift32, shift64, evalLogical]

/-- `orr w0, w2, w0`. -/
theorem r_orr20 (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.logicalShift .W32 .ORR (.gpr 0#5) (.gpr 2#5) (.gpr 0#5) .LSL 0))
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps (((x2 ||| x0).setWidth 32).setWidth 64) x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_logicalShift]
  simp only [execLogicalShift, State.readReg, State.readReg32, rd0, rd2, evalLogical,
    shiftVal, State.writeReg, wr0, S_advancePC]
  simp [shiftVal, shift32, shift64, evalLogical]

/-- `and w0, w0, #mask`. -/
theorem r_and0 {mask : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.logicalImm .W32 .AND (.gpr 0#5) (.gpr 0#5) mask))
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps (((x0 &&& mask).setWidth 32).setWidth 64) x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_logicalImm]
  simp only [execLogicalImm, State.readReg, State.readReg32, rd0, evalLogical,
    State.writeReg, wr0, S_advancePC]
  simp [shiftVal, shift32, shift64, evalLogical]

/-- `sub w0, w0, #1`. -/
theorem r_subW0 (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubImm .W32 .SUB (.gpr 0#5) (.gpr 0#5) 0x001#12 false))
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps ((x0.setWidth 32 - 1#32).setWidth 64) x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_addSubImm]
  simp only [execAddSubImm, State.readReg, State.readReg32, rd0, evalAddSub, State.writeReg, wr0,
    S_advancePC]
  simp [AddWithCarry64, AddWithCarry32]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub]
  omega

/-- `ubfx x0, x0, #13, #3`. -/
theorem r_ubfm13 (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.bitfield .W64 .UBFM (.gpr 0#5) (.gpr 0#5) 13 15))
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps ((x0 >>> 13) &&& 7#64) x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_bitfield]
  simp [execBitfield, State.readReg, evalBitfield, State.writeReg]

/-- `ubfx x0, x0, #2, #14`. -/
theorem r_ubfm2 (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.bitfield .W64 .UBFM (.gpr 0#5) (.gpr 0#5) 2 15))
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps ((x0 >>> 2) &&& 0x3fff#64) x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) h
  rw [ex_bitfield]
  simp [execBitfield, State.readReg, evalBitfield, State.writeReg]

/-- `cmp x1, #n`. -/
theorem r_cmpX1 {n : BitVec 12} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.addSubImm .W64 .SUBS .xzr (.gpr 1#5) n false))
    (h : ∀ ps' : PState, ps'.z = decide (x1 = n.setWidth 64) →
      Reach pl X Q (S s0 (pc + 4#64) sp m ps' x0 x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) := by
  refine reach_step (step_S hrun hf ?_) (h (AddWithCarry64 x1 (~~~(n.setWidth 64)) true).2 ?_)
  · rw [ex_addSubImm]
    simp only [execAddSubImm, State.readReg, rd1, evalAddSub, State.writeReg, wr_xzr, S_setPState,
      S_advancePC]
    simp
  · simp only [AddWithCarry64]
    rw [Bool.eq_iff_iff]; simp; bv_omega

theorem r_bne_t {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.bCond .NE off)) (hc : ps.z = false)
    (h : Reach pl X Q (S s0 (pc + off) sp m ps x0 x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) :=
  reach_step (step_S hrun hf (by rw [ex_bCond]; simp [ConditionHolds, hc])) h

theorem r_bne_f {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.bCond .NE off)) (hc : ps.z = true)
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps x0 x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) :=
  reach_step (step_S hrun hf (by rw [ex_bCond]; simp [ConditionHolds, hc])) h

/-- `adrp x1, #off`. -/
theorem r_adrp1 {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.adr true (.gpr 1#5) off))
    (h : Reach pl X Q (S s0 (pc + 4#64) sp m ps x0 ((pc &&& 0xfffffffffffff000#64) + off) x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) :=
  reach_step (step_S hrun hf (by rw [ex_adr]; simp)) h

theorem r_ret (hrun : s0.status = .Running)
    (hf : (prog pl X).fetchMem m pc = some (.ret (.gpr 0x1e#5)))
    (h : Reach pl X Q (S s0 (s0.readReg64 (.gpr 0x1e#5)) sp m ps x0 x1 x2 x3)) :
    Reach pl X Q (S s0 pc sp m ps x0 x1 x2 x3) :=
  reach_step (step_S hrun hf (by rw [ex_ret, rd_hi _ _ _ _ _ _ _ _ _ _ (by decide)]; simp)) h

end Poly1305DebianApi.Verify

end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianApi.Verify

open Arm64 Arm64.Obj Poly1305DebianCt

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

/-- The word `ldrh w1, [x1, #imm]`, decoded by its mask. -/
theorem decode_ldrh1 (w : BitVec 32) (hK : w &&& 0xffc003ff#32 = 0x79400021#32) :
    decode w = some (.ldr .W32 .H16 false (.gpr 1#5)
      (.Offset (.gpr 1#5) (((w.extractLsb' 10 12).zeroExtend 64) <<< 1))) := by
  rw [decode]
  simp (config := {maxSteps := 4000000}) (disch := decide) only [beq_false_of_mask hK,
    beq_false_of_mask' hK, Bool.false_and, Bool.or_false, if_false, Bool.false_eq_true]
  have hb := fun i => (show (w.getLsbD i && (0xffc003ff#32 : BitVec 32).getLsbD i) = _ by
    rw [← BitVec.getLsbD_and, hK])
  have hc : (w &&& 0x3f000000#32 == 0x39000000#32) = true := by
    simp only [beq_iff_eq]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have := hb i
    simp only [BitVec.getLsbD_and] at this ⊢
    interval_cases i <;> simp_all
  have e30 : BitVec.extractLsb' 30 2 w = 1#2 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have := hb (30 + i)
    simp only [BitVec.getLsbD_extractLsb'] at this ⊢
    interval_cases i <;> simp_all
  have e22 : BitVec.extractLsb' 22 2 w = 1#2 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have := hb (22 + i)
    simp only [BitVec.getLsbD_extractLsb'] at this ⊢
    interval_cases i <;> simp_all
  have e0 : BitVec.extractLsb' 0 5 w = 1#5 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have := hb (0 + i)
    simp only [BitVec.getLsbD_extractLsb'] at this ⊢
    interval_cases i <;> simp_all
  have e5 : BitVec.extractLsb' 5 5 w = 1#5 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have := hb (5 + i)
    simp only [BitVec.getLsbD_extractLsb'] at this ⊢
    interval_cases i <;> simp_all
  rw [if_pos hc, e30, e22, e0, e5]
  rfl

/-! ## Page arithmetic -/

theorem hi_bits32 (D : BitVec 64) (h1 : -(2^32:Int) ≤ D.toInt) (h2 : D.toInt < 2^32) :
    ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32 := by
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

theorem pageOf_add_lo (T : BitVec 64) : pageOf T + (T &&& 0xfff#64) = T := by
  apply BitVec.eq_of_toNat_eq
  have h2 : (T &&& 0xfff#64).toNat = T.toNat % 4096 := by
    rw [BitVec.toNat_and]
    have : (0xfff#64 : BitVec 64).toNat = 2 ^ 12 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_add, pageOf_toNat, h2]
  have := T.isLt; omega

/-! ## `ADRP x1` -/

theorem adrpW_mask (D : BitVec 64) : adrpWordOff 0x90000001#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem adrpW_31 (D : BitVec 64) : (adrpWordOff 0x90000001#32 D).getLsbD 31 = true := by
  simp [adrpWordOff]

theorem adrpW_rd (D : BitVec 64) : (adrpWordOff 0x90000001#32 D).extractLsb' 0 5 = 1#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem adrpW_off (D : BitVec 64)
    (hlo : ∀ i, i < 12 → D.getLsbD i = false)
    (hhi : ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32) :
    ((adrpWordOff 0x90000001#32 D).extractLsb' 5 19 ++
      (adrpWordOff 0x90000001#32 D).extractLsb' 29 2).signExtend 64 <<< 12 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getMsbD]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm

theorem decode_adrp1 {P T : BitVec 64} (hr : AdrpInRange P T) :
    decode (adrpWord 0x90000001#32 P T) = some (.adr true (.gpr 1#5) (pageOf T - pageOf P)) := by
  rw [adrpWord, decode_adr_class _ (adrpW_mask _), adrpW_31, adrpW_rd,
    adrpW_off _ (lo_bits T P) (hi_bits32 _ hr.1 hr.2)]
  rfl

/-! ## `LDRH w1, [x1, :lo12:]` -/

theorem lo12W_mask (T : BitVec 64) : lo12Word 1 0x79400021#32 T &&& 0xffc003ff#32 = 0x79400021#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem lo12_imm (T : BitVec 64) (hal : T &&& 1#64 = 0#64) :
    ((lo12Word 1 0x79400021#32 T).extractLsb' 10 12).zeroExtend 64 <<< 1 = T &&& 0xfff#64 := by
  have hb : T.getLsbD 0 = false := by
    have := congrArg (fun x => x.getLsbD 0) hal
    simpa using this
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;> exact hb

theorem decode_ldrh1_lo12 (T : BitVec 64) (hal : Lo12Aligned 1 T) :
    decode (lo12Word 1 0x79400021#32 T) =
      some (.ldr .W32 .H16 false (.gpr 1#5) (.Offset (.gpr 1#5) (T &&& 0xfff#64))) := by
  rw [decode_ldrh1 _ (lo12W_mask T), lo12_imm T hal]

/-! ## The two relocated sites of each function -/

/-- The address of `optblocker_u16`. -/
abbrev OB : String := "optblocker_u16 [libsodium_la_verify]"

theorem lookup_OB : lookup OB TXT.symbols = none := by decide

theorem target_OB (pl : Placement) (o : Nat) (k : RelocKind) :
    TXT.target pl { off := o, kind := k, sym := OB } = pl.ρ OB := by
  simp [CodeBlock.target, CodeBlock.resolve, lookup_OB, addSignedAddr]

theorem relocTarget_OB (pl : Placement) (o : Nat) (k : RelocKind) (hk : (k == .call26 || k == .jump26) = false) :
    TXT.relocTarget pl o { off := o, kind := k, sym := OB } = pl.ρ OB := by
  simp only [CodeBlock.relocTarget, CodeBlock.b2bNext?, hk, Bool.false_eq_true, if_false, ite_self]
  exact target_OB pl o k

/-- The `adrp x1, optblocker_u16` at `off`. -/
theorem pw_adrp (pl : Placement) (off : Nat)
    (hr : TXT.relocAt? off = some { off := off, kind := .adrpHi21, sym := OB })
    (hw : TXT.wordAt off = 0x90000001#32)
    (hrel1 : TXT.relaxableAt off = false) (hrel2 : TXT.relaxableAt (off - 4) = false) :
    TXT.patchedWord pl off = adrpWord 0x90000001#32 (pl.base + BitVec.ofNat 64 off) (pl.ρ OB) := by
  have h1 : TXT.relaxedAt pl off = false := by simp [CodeBlock.relaxedAt, hrel1]
  have h2 : TXT.relaxedAt pl (off - 4) = false := by simp [CodeBlock.relaxedAt, hrel2]
  have hu : TXT.undefWeakBranch pl { off := off, kind := .adrpHi21, sym := OB } = false := by
    simp [CodeBlock.undefWeakBranch]
  rw [CodeBlock.patchedWord]
  simp only [hr, h1, h2, hw, hu, relocTarget_OB pl off .adrpHi21 rfl, Bool.false_eq_true, if_false,
    Bool.and_false]
  simp [RelocKind.isGotOrTlsIe, patchRelocWord]

/-- The `ldrh w1, [x1, :lo12:optblocker_u16]` at `off`. -/
theorem pw_ldrh (pl : Placement) (off : Nat)
    (hr : TXT.relocAt? off = some { off := off, kind := .ldst16Lo12, sym := OB })
    (hw : TXT.wordAt off = 0x79400021#32)
    (hrel1 : TXT.relaxableAt off = false) (hrel2 : TXT.relaxableAt (off - 4) = false) :
    TXT.patchedWord pl off = lo12Word 1 0x79400021#32 (pl.ρ OB) := by
  have h1 : TXT.relaxedAt pl off = false := by simp [CodeBlock.relaxedAt, hrel1]
  have h2 : TXT.relaxedAt pl (off - 4) = false := by simp [CodeBlock.relaxedAt, hrel2]
  have hu : TXT.undefWeakBranch pl { off := off, kind := .ldst16Lo12, sym := OB } = false := by
    simp [CodeBlock.undefWeakBranch]
  rw [CodeBlock.patchedWord]
  simp only [hr, h1, h2, hw, hu, relocTarget_OB pl off .ldst16Lo12 rfl, Bool.false_eq_true, if_false,
    Bool.and_false]
  simp [RelocKind.isGotOrTlsIe, patchRelocWord]

/-- The range facts `Placeable` gives for a relocation of `OB` at `off`. -/
theorem range_OB {pl : Placement} (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl) {off : Nat}
    {k : RelocKind} (hk : (k == .call26 || k == .jump26) = false)
    (hmem : ({ off := off, kind := k, sym := OB } : RelocEntry) ∈ TXT.relocs) :
    TXT.relocInRange pl k off (pl.base + BitVec.ofNat 64 off) (pl.ρ OB) := by
  have h := (hP.text.relocs_ok _ hmem).2.2
  change TXT.relocInRange pl k off _ (TXT.relocTarget pl off { off := off, kind := k, sym := OB }) at h
  rw [relocTarget_OB pl off k hk] at h
  exact h

theorem fetch_adrp {pl : Placement} (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {X : String → Option (State → State)} {m : Memory} (hCL : (prog pl X).CodeLoaded m) (off : Nat)
    (hal : off % 4 = 0 ∧ off + 4 ≤ 2324)
    (hr : TXT.relocAt? off = some { off := off, kind := .adrpHi21, sym := OB })
    (hmem : ({ off := off, kind := .adrpHi21, sym := OB } : RelocEntry) ∈ TXT.relocs)
    (hw : TXT.wordAt off = 0x90000001#32)
    (hrel1 : TXT.relaxableAt off = false) (hrel2 : TXT.relaxableAt (off - 4) = false) :
    (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      some (.adr true (.gpr 1#5) (pageOf (pl.ρ OB) - pageOf (pl.base + BitVec.ofNat 64 off))) := by
  rw [fetch_word hP hCL hal.1 hal.2, pw_adrp pl off hr hw hrel1 hrel2]
  have h := range_OB hP (k := .adrpHi21) rfl hmem
  exact decode_adrp1 h

theorem fetch_ldrh {pl : Placement} (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {X : String → Option (State → State)} {m : Memory} (hCL : (prog pl X).CodeLoaded m) (off : Nat)
    (hal : off % 4 = 0 ∧ off + 4 ≤ 2324)
    (hr : TXT.relocAt? off = some { off := off, kind := .ldst16Lo12, sym := OB })
    (hmem : ({ off := off, kind := .ldst16Lo12, sym := OB } : RelocEntry) ∈ TXT.relocs)
    (hw : TXT.wordAt off = 0x79400021#32)
    (hrel1 : TXT.relaxableAt off = false) (hrel2 : TXT.relaxableAt (off - 4) = false) :
    (prog pl X).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      some (.ldr .W32 .H16 false (.gpr 1#5) (.Offset (.gpr 1#5) (pl.ρ OB &&& 0xfff#64))) := by
  rw [fetch_word hP hCL hal.1 hal.2, pw_ldrh pl off hr hw hrel1 hrel2]
  have h := range_OB hP (k := .ldst16Lo12) rfl hmem
  exact decode_ldrh1_lo12 _ h

end Poly1305DebianApi.Verify

end
end

section
section
/-! # The values: one loop iteration, the accumulator, and the epilogue's arithmetic -/

set_option autoImplicit false

namespace Poly1305DebianApi.Verify

open Arm64 Arm64.Obj Poly1305DebianCt

/-- The halfword the loop body stores (`eor w0, w0, w3; and w0, w0, #0xff; orr w0, w2, w0;
strh w0`), with `w0 = b`, `w3 = a`, `w2 = acc`. -/
theorem loop_val (a b acc : BitVec 8) :
    ((((((acc.setWidth 16).setWidth 64 |||
      ((((b.setWidth 64 ^^^ a.setWidth 64).setWidth 32).setWidth 64 &&& 0x000000ff000000ff#64).setWidth 32).setWidth 64)
      ).setWidth 32).setWidth 64).setWidth 16) = (acc ||| (a ^^^ b)).setWidth 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  interval_cases i <;> simp [Bool.xor_comm]

/-- The OR of the bytewise differences of `ga` and `gb` below `i`. -/
def acc8 (ga gb : Nat → BitVec 8) : Nat → BitVec 8
  | 0 => 0#8
  | i + 1 => acc8 ga gb i ||| (ga i ^^^ gb i)

theorem acc8_eq_zero (ga gb : Nat → BitVec 8) :
    ∀ n, acc8 ga gb n = 0#8 ↔ ∀ j < n, ga j = gb j
  | 0 => by simp [acc8]
  | n + 1 => by
    rw [acc8, BitVec.or_eq_zero_iff, acc8_eq_zero ga gb n, BitVec.xor_eq_zero_iff]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact h1 j h
      · subst h; exact h2
    · intro h; exact ⟨fun j hj => h j (by omega), h n (by omega)⟩

end Poly1305DebianApi.Verify

end
end

section
section
/-! # The run of `crypto_verify_n`, generic in the entry offset `E`, the loop offset `L` and `n`

`Code pl X E L n` lists the instruction at every address of the function (the three functions
differ only in the padding `nop`s before the loop and in the loop bound). `Hyp` collects what the
precondition gives about the entry state. `run` reaches the return with `w0 = okResult (a = b)`. -/

set_option autoImplicit false

namespace Poly1305DebianApi.Verify

open Arm64 Arm64.Obj Poly1305DebianCt

abbrev A (pl : Placement) (k : Nat) : BitVec 64 := pl.base + BitVec.ofNat 64 k

abbrev CL (pl : Placement) (X : String → Option (State → State)) (m : Memory) : Prop :=
  (prog pl X).CodeLoaded m

/-- The instructions of one `crypto_verify_n`. -/
structure Code (pl : Placement) (X : String → Option (State → State)) (E L : Nat) (nb : BitVec 12) :
    Prop where
  e0 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl E) = some (.hint 0x22#7)
  e1 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (E + 4)) =
    some (.addSubImm .W64 .SUB .sp .sp 0x020#12 false)
  e2 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (E + 8)) =
    some (.str .X64 (.gpr 0#5) (.Offset .sp 0x10#64))
  e3 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (E + 12)) =
    some (.str .X64 (.gpr 1#5) (.Offset .sp 0x18#64))
  e4 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (E + 16)) =
    some (.moveWide .W64 .MOVZ (.gpr 1#5) 0x0000#16 0)
  e5 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (E + 20)) =
    some (.str .H16 .xzr (.Offset .sp 0xe#64))
  pad : L = E + 24 ∨ (L = E + 32 ∧
    (∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (E + 24)) = some .nop) ∧
    (∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (E + 28)) = some .nop))
  l0 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl L) =
    some (.ldr .W64 .X64 false (.gpr 0#5) (.Offset .sp 0x10#64))
  l1 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 4)) =
    some (.ldr .W32 .B8 false (.gpr 3#5) (.RegOffset (.gpr 0#5) (.gpr 1#5) .UXTX 0))
  l2 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 8)) =
    some (.ldr .W64 .X64 false (.gpr 0#5) (.Offset .sp 0x18#64))
  l3 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 12)) =
    some (.ldr .W32 .B8 false (.gpr 0#5) (.RegOffset (.gpr 0#5) (.gpr 1#5) .UXTX 0))
  l4 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 16)) =
    some (.addSubImm .W64 .ADD (.gpr 1#5) (.gpr 1#5) 0x001#12 false)
  l5 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 20)) =
    some (.ldr .W32 .H16 false (.gpr 2#5) (.Offset .sp 0xe#64))
  l6 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 24)) =
    some (.logicalShift .W32 .EOR (.gpr 0#5) (.gpr 0#5) (.gpr 3#5) .LSL 0)
  l7 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 28)) =
    some (.logicalImm .W32 .AND (.gpr 0#5) (.gpr 0#5) 0x000000ff000000ff#64)
  l8 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 32)) =
    some (.logicalShift .W32 .ORR (.gpr 0#5) (.gpr 2#5) (.gpr 0#5) .LSL 0)
  l9 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 36)) =
    some (.str .H16 (.gpr 0#5) (.Offset .sp 0xe#64))
  l10 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 40)) =
    some (.addSubImm .W64 .SUBS .xzr (.gpr 1#5) nb false)
  l11 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 44)) =
    some (.bCond .NE 0xffffffffffffffd4#64)
  p0 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 48)) =
    some (.ldr .W32 .H16 false (.gpr 0#5) (.Offset .sp 0xe#64))
  p1 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 52)) =
    some (.str .H16 (.gpr 0#5) (.Offset .sp 0xe#64))
  p2 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 56)) =
    some (.adr true (.gpr 1#5) (pageOf (pl.ρ OB) - pageOf (A pl (L + 56))))
  p3 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 60)) =
    some (.ldr .W32 .H16 false (.gpr 0#5) (.Offset .sp 0xe#64))
  p4 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 64)) =
    some (.addSubImm .W32 .SUB (.gpr 0#5) (.gpr 0#5) 0x001#12 false)
  p5 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 68)) =
    some (.str .H16 (.gpr 0#5) (.Offset .sp 0xe#64))
  p6 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 72)) =
    some (.ldr .W32 .H16 false (.gpr 0#5) (.Offset .sp 0xe#64))
  p7 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 76)) =
    some (.ldr .W32 .H16 false (.gpr 1#5) (.Offset (.gpr 1#5) (pl.ρ OB &&& 0xfff#64)))
  p8 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 80)) =
    some (.bitfield .W64 .UBFM (.gpr 0#5) (.gpr 0#5) 13 15)
  p9 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 84)) =
    some (.logicalShift .W32 .EOR (.gpr 0#5) (.gpr 0#5) (.gpr 1#5) .LSL 0)
  p10 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 88)) =
    some (.bitfield .W64 .UBFM (.gpr 0#5) (.gpr 0#5) 2 15)
  p11 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 92)) =
    some (.str .H16 (.gpr 0#5) (.Offset .sp 0xe#64))
  p12 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 96)) =
    some (.ldr .W32 .H16 false (.gpr 0#5) (.Offset .sp 0xe#64))
  p13 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 100)) =
    some (.addSubImm .W64 .ADD .sp .sp 0x020#12 false)
  p14 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 104)) =
    some (.logicalImm .W32 .AND (.gpr 0#5) (.gpr 0#5) 0x0000ffff0000ffff#64)
  p15 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 108)) =
    some (.addSubImm .W32 .SUB (.gpr 0#5) (.gpr 0#5) 0x001#12 false)
  p16 : ∀ m, CL pl X m → (prog pl X).fetchMem m (A pl (L + 112)) = some (.ret (.gpr 0x1e#5))
  hL : L + 116 < 2 ^ 64

/-- A readable byte outside the frame, with its value. -/
def Rd (s0 : State) (a : BitVec 64) (v : BitVec 8) : Prop :=
  ¬ W s0 a ∧ (s0.mem.perm a).r = true ∧ s0.mem.isLazyFree a = false ∧ s0.mem.read8 a = v

/-- What the precondition gives about the entry state. -/
structure Hyp (pl : Placement) (X : String → Option (State → State)) (s0 : State) (n : Nat)
    (ga gb : Nat → BitVec 8) : Prop where
  hP : libsodiumDebianOnetimeauthCtLib.Placeable pl
  hCL : CL pl X s0.mem
  hrun : s0.status = .Running
  sp_al : (s0.sp &&& 0b1111#64 == 0#64) = true
  ok : MemOk s0 s0.mem
  xa : ∀ j < n, Rd s0 (s0.readReg64 (.gpr 0#5) + BitVec.ofNat 64 j) (ga j)
  yb : ∀ j < n, Rd s0 (s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 j) (gb j)
  ob : ∀ k < 2, Rd s0 (pl.ρ OB + BitVec.ofNat 64 k) 0#8

/-- The return: `pc = lr`, `sp` restored, memory changed only in the frame, `w0 = okResult ok`. -/
def Fin (s0 : State) (ok : Bool) (sf : State) : Prop :=
  ∃ mF ps x0 x1 x2 x3, sf = S s0 (s0.readReg64 (.gpr 0x1e#5)) s0.sp mF ps x0 x1 x2 x3 ∧
    MemOk s0 mF ∧ x0.setWidth 32 = okResult ok

theorem nx {pl : Placement} {X : String → Option (State → State)} {Q : State → Prop} {s0 : State}
    {sp : BitVec 64} {m : Memory} {ps : PState} {x0 x1 x2 x3 : BitVec 64} (k' : Nat) {k : Nat}
    (h : Reach pl X Q (S s0 (A pl k') sp m ps x0 x1 x2 x3)) (hk : k + 4 = k' := by omega) :
    Reach pl X Q (S s0 (A pl k + 4#64) sp m ps x0 x1 x2 x3) := by
  subst hk
  rwa [show A pl k + 4#64 = A pl (k + 4) by
    simp only [A]; rw [BitVec.add_assoc, BitVec.ofNat_add]]

theorem toNat_and15 (y : BitVec 64) : (y &&& 0b1111#64).toNat = y.toNat % 16 := by
  rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod y.toNat 4

theorem B_al (s0 : State) (h : (s0.sp &&& 0b1111#64 == 0#64) = true) :
    (B s0 &&& 0b1111#64 == 0#64) = true := by
  simp only [beq_iff_eq] at h ⊢
  have h1 := congrArg BitVec.toNat h
  rw [toNat_and15] at h1
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and15, B, BitVec.toNat_sub]
  have := s0.sp.isLt
  simp at h1 ⊢; omega

theorem B_add32 (s0 : State) : B s0 + 32#64 = s0.sp := BitVec.sub_add_cancel _ _

theorem canRead_Rd {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} {v : BitVec 8}
    (h : Rd s0 a v) : m.canRead a 1 = true :=
  canRead_notW hm fun k hk => by
    have : k = 0 := by omega
    subst this; simpa using ⟨h.1, h.2.1, h.2.2.1⟩

theorem read8_Rd {s0 : State} {m : Memory} (hm : MemOk s0 m) {a : BitVec 64} {v : BitVec 8}
    (h : Rd s0 a v) : m.read8 a = v := by
  rw [read8_of_notW hm h.1]; exact h.2.2.2

/-- The epilogue's value, as the run computes it, for accumulator `d`. -/
def epiX (d : BitVec 8) : BitVec 32 :=
  let v2 : BitVec 64 :=
    ((((((d.setWidth 16).setWidth 64).setWidth 16).setWidth 64).setWidth 32 - 1#32).setWidth 64)
  let v3 : BitVec 64 := ((((v2.setWidth 16).setWidth 64 >>> 13 &&& 7#64) ^^^
    (0#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64 >>> 2 &&& 0x3fff#64
  BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
    (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 16 v3) &&& 281470681808895#64))) - 1#32))

theorem epiX_all : ∀ k < 256, epiX (BitVec.ofNat 8 k) = okResult (decide (BitVec.ofNat 8 k = 0#8)) := by
  decide +kernel

theorem epiX_eq (d : BitVec 8) : epiX d = okResult (decide (d = 0#8)) := by
  have := epiX_all d.toNat d.isLt
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

section run

variable {pl : Placement} {X : String → Option (State → State)} {s0 : State} {n : Nat}
  {ga gb : Nat → BitVec 8} {E L : Nat} {nb : BitVec 12}

theorem cl_of (H : Hyp pl X s0 n ga gb) {m : Memory} (hm : MemOk s0 m) : CL pl X m :=
  Good.codeLoaded ⟨H.hP, H.hCL, hm⟩

/-- The epilogue, from the loop's exit with accumulator `d`. -/
theorem epilogue (H : Hyp pl X s0 n ga gb) (C : Code pl X E L nb) (d : BitVec 8)
    {m : Memory} {ps : PState} {x0 x1 x2 x3 : BitVec 64}
    (F : Fr s0 m (s0.readReg64 (.gpr 0#5)) (s0.readReg64 (.gpr 1#5)) (d.setWidth 16)) :
    Reach pl X (Fin s0 (decide (d = 0#8))) (S s0 (A pl (L + 48)) (B s0) m ps x0 x1 x2 x3) := by
  have hal := B_al s0 H.sp_al
  have hrun := H.hrun
  -- ldrh w0, [sp, #0xe]
  refine r_ldrh0 hrun (C.p0 m (cl_of H F.ok)) hal (canRead_frame F.ok 14 2 (by omega)) ?_
  refine nx (L + 52) ?_
  rw [F.sd]
  -- strh w0, [sp, #0xe]
  have F1 := F.write16 (((d.setWidth 16).setWidth 64).setWidth 16)
  refine r_strh0 hrun (C.p1 m (cl_of H F.ok)) hal (canWrite_frame F.ok 14 2 (by omega)) ?_
  refine nx (L + 56) ?_
  -- adrp x1
  refine r_adrp1 hrun (C.p2 _ (cl_of H F1.ok)) ?_
  refine nx (L + 60) ?_
  -- ldrh w0
  refine r_ldrh0 hrun (C.p3 _ (cl_of H F1.ok)) hal (canRead_frame F1.ok 14 2 (by omega)) ?_
  refine nx (L + 64) ?_
  rw [F1.sd]
  -- sub w0, w0, #1
  refine r_subW0 hrun (C.p4 _ (cl_of H F1.ok)) ?_
  refine nx (L + 68) ?_
  -- strh w0
  generalize hv2 : ((((((d.setWidth 16).setWidth 64).setWidth 16).setWidth 64).setWidth 32 - 1#32).setWidth 64) = v2
  have F2 := F1.write16 (v2.setWidth 16)
  refine r_strh0 hrun (C.p5 _ (cl_of H F1.ok)) hal (canWrite_frame F1.ok 14 2 (by omega)) ?_
  refine nx (L + 72) ?_
  -- ldrh w0
  refine r_ldrh0 hrun (C.p6 _ (cl_of H F2.ok)) hal (canRead_frame F2.ok 14 2 (by omega)) ?_
  refine nx (L + 76) ?_
  rw [F2.sd]
  -- ldrh w1, [x1, :lo12:optblocker_u16]
  rw [show (A pl (L + 56) &&& 0xfffffffffffff000#64) + (pageOf (pl.ρ OB) - pageOf (A pl (L + 56)))
      = pageOf (pl.ρ OB) by
    rw [show A pl (L + 56) &&& 0xfffffffffffff000#64 = pageOf (A pl (L + 56)) from rfl,
      BitVec.add_comm, BitVec.sub_add_cancel]]
  have hr2 : (((m.write16 (B s0 + 14#64) (((d.setWidth 16).setWidth 64).setWidth 16)).write16
      (B s0 + 14#64) (v2.setWidth 16))).canRead (pl.ρ OB) 2 = true :=
    canRead_notW F2.ok fun k hk => ⟨(H.ob k hk).1, (H.ob k hk).2.1, (H.ob k hk).2.2.1⟩
  refine r_ldrh1 hrun (C.p7 _ (cl_of H F2.ok)) (by rw [pageOf_add_lo]; exact hr2) ?_
  refine nx (L + 80) ?_
  rw [pageOf_add_lo]
  have e16 : ((m.write16 (B s0 + 14#64) (((d.setWidth 16).setWidth 64).setWidth 16)).write16
      (B s0 + 14#64) (v2.setWidth 16)).read16 (pl.ρ OB) = 0#16 := by
    simp only [Memory.read16]
    rw [read8_Rd F2.ok (H.ob 0 (by omega)), read8_Rd F2.ok (H.ob 1 (by omega))]; rfl
  rw [e16]
  refine r_ubfm13 hrun (C.p8 _ (cl_of H F2.ok)) ?_
  refine nx (L + 84) ?_
  refine r_eor01 hrun (C.p9 _ (cl_of H F2.ok)) ?_
  refine nx (L + 88) ?_
  refine r_ubfm2 hrun (C.p10 _ (cl_of H F2.ok)) ?_
  refine nx (L + 92) ?_
  generalize hv3 : ((((v2.setWidth 16).setWidth 64 >>> 13 &&& 7#64) ^^^ (0#16 : BitVec 16).setWidth 64).setWidth 32).setWidth 64 >>> 2 &&& 0x3fff#64 = v3
  have F3 := F2.write16 (v3.setWidth 16)
  refine r_strh0 hrun (C.p11 _ (cl_of H F2.ok)) hal (canWrite_frame F2.ok 14 2 (by omega)) ?_
  refine nx (L + 96) ?_
  refine r_ldrh0 hrun (C.p12 _ (cl_of H F3.ok)) hal (canRead_frame F3.ok 14 2 (by omega)) ?_
  refine nx (L + 100) ?_
  rw [F3.sd]
  refine r_addSp hrun (C.p13 _ (cl_of H F3.ok)) ?_
  refine nx (L + 104) ?_
  refine r_and0 hrun (C.p14 _ (cl_of H F3.ok)) ?_
  refine nx (L + 108) ?_
  refine r_subW0 hrun (C.p15 _ (cl_of H F3.ok)) ?_
  refine nx (L + 112) ?_
  refine r_ret hrun (C.p16 _ (cl_of H F3.ok)) ?_
  refine reach_done ⟨_, _, _, _, _, _, by rw [B_add32], F3.ok, ?_⟩
  subst hv3; subst hv2
  exact epiX_eq d

theorem bne_back (pl : Placement) (L : Nat) (hL : L + 116 < 2 ^ 64) :
    A pl (L + 44) + 0xffffffffffffffd4#64 = A pl L := by
  have e : BitVec.ofNat 64 (L + 44) + 0xffffffffffffffd4#64 = BitVec.ofNat 64 L := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  show pl.base + BitVec.ofNat 64 (L + 44) + 0xffffffffffffffd4#64 = pl.base + BitVec.ofNat 64 L
  rw [BitVec.add_assoc, e]

/-- One iteration of the loop, then either the next iteration or the epilogue. -/
theorem loop (H : Hyp pl X s0 n ga gb) (C : Code pl X E L nb) (hnb : nb.toNat = n) :
    ∀ j i, i + j = n → i < n → ∀ (m : Memory) (ps : PState) (x0 x2 x3 : BitVec 64),
      Fr s0 m (s0.readReg64 (.gpr 0#5)) (s0.readReg64 (.gpr 1#5)) ((acc8 ga gb i).setWidth 16) →
      Reach pl X (Fin s0 (decide (acc8 ga gb n = 0#8)))
        (S s0 (A pl L) (B s0) m ps x0 (BitVec.ofNat 64 i) x2 x3)
  | 0, i, hij, hi, _, _, _, _, _, _ => by omega
  | j + 1, i, hij, hi, m, ps, x0, x2, x3, F => by
    have hal := B_al s0 H.sp_al
    have hrun := H.hrun
    have hn64 : n < 4096 := hnb ▸ nb.isLt
    refine r_ldrX0 hrun (C.l0 m (cl_of H F.ok)) hal (canRead_frame F.ok 16 8 (by omega)) ?_
    refine nx (L + 4) ?_
    rw [show (0x10#64 : BitVec 64) = 16#64 from rfl, F.sx]
    refine r_ldrb3 hrun (C.l1 m (cl_of H F.ok)) (canRead_Rd F.ok (H.xa i hi)) ?_
    refine nx (L + 8) ?_
    rw [read8_Rd F.ok (H.xa i hi)]
    refine r_ldrX0 hrun (C.l2 m (cl_of H F.ok)) hal (canRead_frame F.ok 24 8 (by omega)) ?_
    refine nx (L + 12) ?_
    rw [show (0x18#64 : BitVec 64) = 24#64 from rfl, F.sy]
    refine r_ldrb0 hrun (C.l3 m (cl_of H F.ok)) (canRead_Rd F.ok (H.yb i hi)) ?_
    refine nx (L + 16) ?_
    rw [read8_Rd F.ok (H.yb i hi)]
    refine r_incX1 hrun (C.l4 m (cl_of H F.ok)) ?_
    refine nx (L + 20) ?_
    refine r_ldrh2 hrun (C.l5 m (cl_of H F.ok)) hal (canRead_frame F.ok 14 2 (by omega)) ?_
    refine nx (L + 24) ?_
    rw [show (0xe#64 : BitVec 64) = 14#64 from rfl, F.sd]
    refine r_eor03 hrun (C.l6 m (cl_of H F.ok)) ?_
    refine nx (L + 28) ?_
    refine r_and0 hrun (C.l7 m (cl_of H F.ok)) ?_
    refine nx (L + 32) ?_
    refine r_orr20 hrun (C.l8 m (cl_of H F.ok)) ?_
    refine nx (L + 36) ?_
    refine r_strh0 hrun (C.l9 m (cl_of H F.ok)) hal (canWrite_frame F.ok 14 2 (by omega)) ?_
    refine nx (L + 40) ?_
    rw [show (0xe#64 : BitVec 64) = 14#64 from rfl, loop_val]
    have F' := F.write16 ((acc8 ga gb i ||| (ga i ^^^ gb i)).setWidth 16)
    refine r_cmpX1 hrun (C.l10 _ (cl_of H F'.ok)) fun ps' hz => ?_
    refine nx (L + 44) ?_
    have hx1 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
      rw [BitVec.ofNat_add]
    rw [hx1] at hz ⊢
    have hiff : (BitVec.ofNat 64 (i + 1) = nb.setWidth 64) ↔ i + 1 = n := by
      constructor
      · intro e; have := congrArg BitVec.toNat e
        simp [BitVec.toNat_setWidth] at this; omega
      · intro e; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]; omega
    by_cases hlast : i + 1 = n
    · have hz' : ps'.z = true := by rw [hz]; exact decide_eq_true (hiff.mpr hlast)
      refine r_bne_f hrun (C.l11 _ (cl_of H F'.ok)) hz' ?_
      refine nx (L + 48) ?_
      exact epilogue H C (acc8 ga gb n) (by rw [← hlast]; exact F')
    · have hz' : ps'.z = false := by rw [hz]; exact decide_eq_false (fun e => hlast (hiff.mp e))
      refine r_bne_t hrun (C.l11 _ (cl_of H F'.ok)) hz' ?_
      rw [bne_back pl L C.hL]
      exact loop H C hnb j (i + 1) (by omega) (by omega) _ _ _ _ _ F'

/-- The whole function, from its entry `A pl E`. -/
theorem run (H : Hyp pl X s0 n ga gb) (C : Code pl X E L nb) (hnb : nb.toNat = n) (hn : 0 < n)
    (hpc : s0.pc = A pl E) :
    Reach pl X (Fin s0 (decide (acc8 ga gb n = 0#8))) s0 := by
  have hal := B_al s0 H.sp_al
  have hrun := H.hrun
  suffices h : Reach pl X (Fin s0 (decide (acc8 ga gb n = 0#8))) (S s0 (A pl E) s0.sp s0.mem s0.pstate
      (s0.readReg64 (.gpr 0#5)) (s0.readReg64 (.gpr 1#5)) (s0.readReg64 (.gpr 2#5))
      (s0.readReg64 (.gpr 3#5))) by
    rw [← hpc, S_self] at h; exact h
  refine r_hint hrun (C.e0 _ H.hCL) ?_
  refine nx (E + 4) ?_
  refine r_subSp hrun (C.e1 _ H.hCL) ?_
  refine nx (E + 8) ?_
  have ok1 := memOk_write64 H.ok 16 (by omega) (s0.readReg64 (.gpr 0#5))
  refine r_strX0 hrun (C.e2 _ H.hCL) hal (canWrite_frame H.ok 16 8 (by omega)) ?_
  refine nx (E + 12) ?_
  have ok2 := memOk_write64 ok1 24 (by omega) (s0.readReg64 (.gpr 1#5))
  refine r_strX1 hrun (C.e3 _ (cl_of H ok1)) hal (canWrite_frame ok1 24 8 (by omega)) ?_
  refine nx (E + 16) ?_
  refine r_movX1 hrun (C.e4 _ (cl_of H ok2)) ?_
  refine nx (E + 20) ?_
  refine r_strhZ hrun (C.e5 _ (cl_of H ok2)) hal (canWrite_frame ok2 14 2 (by omega)) ?_
  have F0 : Fr s0 (((s0.mem.write64 (B s0 + 16#64) (s0.readReg64 (.gpr 0#5))).write64 (B s0 + 24#64)
      (s0.readReg64 (.gpr 1#5))).write16 (B s0 + 14#64) 0#16) (s0.readReg64 (.gpr 0#5))
      (s0.readReg64 (.gpr 1#5)) ((acc8 ga gb 0).setWidth 16) := by
    refine ⟨memOk_write16 ok2 14 (by omega) _, ?_, ?_, ?_⟩
    · rw [read64_16_write16_14, read64_16_write64_24, read64_write64_same]
    · rw [read64_24_write16_14, read64_write64_same]
    · rw [read16_write16_same]; rfl
  have hL := loop H C hnb n 0 (by omega) hn _ s0.pstate (s0.readReg64 (.gpr 0#5))
    (s0.readReg64 (.gpr 2#5)) (s0.readReg64 (.gpr 3#5)) F0
  rcases C.pad with hp | ⟨hp, n1, n2⟩
  · refine nx (E + 24) ?_
    rw [← hp]; exact hL
  · refine nx (E + 24) ?_
    refine r_nop hrun (n1 _ (cl_of H F0.ok)) ?_
    refine nx (E + 28) ?_
    refine r_nop hrun (n2 _ (cl_of H F0.ok)) ?_
    refine nx (E + 32) ?_
    rw [← hp]; exact hL

end run

end Poly1305DebianApi.Verify

end
end

section
section
/-! # The instructions of `crypto_verify_16`, `_32` and `_64` (`Code` instances)

Each unrelocated word is decoded by `decide +kernel`; the `adrp`/`ldrh` pair of each function is
relocated against `optblocker_u16` (`fetch_adrp`, `fetch_ldrh`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianApi.Verify

open Arm64 Arm64.Obj Poly1305DebianCt

theorem fw {pl : Placement} (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    {X : String → Option (State → State)} {m : Memory} (hCL : CL pl X m) (off : Nat) {I : Instr}
    (hal : off % 4 = 0 := by decide) (hlen : off + 4 ≤ 2324 := by decide)
    (hr : TXT.relocAt? off = none := by decide +kernel)
    (hd : decode (TXT.wordAt off) = some I := by decide +kernel) :
    (prog pl X).fetchMem m (A pl off) = some I := by
  rw [fetch_word hP hCL hal hlen, patchedWord_plain pl hr, hd]

theorem code_16 {pl : Placement} (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    (X : String → Option (State → State)) : Code pl X 1868 1892 0x010#12 :=
  ⟨(fun m h => fw hP h 1868),
    (fun m h => fw hP h (1868 + 4)),
    (fun m h => fw hP h (1868 + 8)),
    (fun m h => fw hP h (1868 + 12)),
    (fun m h => fw hP h (1868 + 16)),
    (fun m h => fw hP h (1868 + 20)),
    (Or.inl rfl),
    (fun m h => fw hP h 1892),
    (fun m h => fw hP h (1892 + 4)),
    (fun m h => fw hP h (1892 + 8)),
    (fun m h => fw hP h (1892 + 12)),
    (fun m h => fw hP h (1892 + 16)),
    (fun m h => fw hP h (1892 + 20)),
    (fun m h => fw hP h (1892 + 24)),
    (fun m h => fw hP h (1892 + 28)),
    (fun m h => fw hP h (1892 + 32)),
    (fun m h => fw hP h (1892 + 36)),
    (fun m h => fw hP h (1892 + 40)),
    (fun m h => fw hP h (1892 + 44)),
    (fun m h => fw hP h (1892 + 48)),
    (fun m h => fw hP h (1892 + 52)),
    (fun m h => fetch_adrp hP h (1892 + 56) ⟨by decide, by decide⟩ (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)),
    (fun m h => fw hP h (1892 + 60)),
    (fun m h => fw hP h (1892 + 64)),
    (fun m h => fw hP h (1892 + 68)),
    (fun m h => fw hP h (1892 + 72)),
    (fun m h => fetch_ldrh hP h (1892 + 76) ⟨by decide, by decide⟩ (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)),
    (fun m h => fw hP h (1892 + 80)),
    (fun m h => fw hP h (1892 + 84)),
    (fun m h => fw hP h (1892 + 88)),
    (fun m h => fw hP h (1892 + 92)),
    (fun m h => fw hP h (1892 + 96)),
    (fun m h => fw hP h (1892 + 100)),
    (fun m h => fw hP h (1892 + 104)),
    (fun m h => fw hP h (1892 + 108)),
    (fun m h => fw hP h (1892 + 112)),
    (by decide)⟩

theorem code_32 {pl : Placement} (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    (X : String → Option (State → State)) : Code pl X 2016 2048 0x020#12 :=
  ⟨(fun m h => fw hP h 2016),
    (fun m h => fw hP h (2016 + 4)),
    (fun m h => fw hP h (2016 + 8)),
    (fun m h => fw hP h (2016 + 12)),
    (fun m h => fw hP h (2016 + 16)),
    (fun m h => fw hP h (2016 + 20)),
    (Or.inr ⟨rfl, fun m h => fw hP h (2016 + 24), fun m h => fw hP h (2016 + 28)⟩),
    (fun m h => fw hP h 2048),
    (fun m h => fw hP h (2048 + 4)),
    (fun m h => fw hP h (2048 + 8)),
    (fun m h => fw hP h (2048 + 12)),
    (fun m h => fw hP h (2048 + 16)),
    (fun m h => fw hP h (2048 + 20)),
    (fun m h => fw hP h (2048 + 24)),
    (fun m h => fw hP h (2048 + 28)),
    (fun m h => fw hP h (2048 + 32)),
    (fun m h => fw hP h (2048 + 36)),
    (fun m h => fw hP h (2048 + 40)),
    (fun m h => fw hP h (2048 + 44)),
    (fun m h => fw hP h (2048 + 48)),
    (fun m h => fw hP h (2048 + 52)),
    (fun m h => fetch_adrp hP h (2048 + 56) ⟨by decide, by decide⟩ (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)),
    (fun m h => fw hP h (2048 + 60)),
    (fun m h => fw hP h (2048 + 64)),
    (fun m h => fw hP h (2048 + 68)),
    (fun m h => fw hP h (2048 + 72)),
    (fun m h => fetch_ldrh hP h (2048 + 76) ⟨by decide, by decide⟩ (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)),
    (fun m h => fw hP h (2048 + 80)),
    (fun m h => fw hP h (2048 + 84)),
    (fun m h => fw hP h (2048 + 88)),
    (fun m h => fw hP h (2048 + 92)),
    (fun m h => fw hP h (2048 + 96)),
    (fun m h => fw hP h (2048 + 100)),
    (fun m h => fw hP h (2048 + 104)),
    (fun m h => fw hP h (2048 + 108)),
    (fun m h => fw hP h (2048 + 112)),
    (by decide)⟩

theorem code_64 {pl : Placement} (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl)
    (X : String → Option (State → State)) : Code pl X 2176 2208 0x040#12 :=
  ⟨(fun m h => fw hP h 2176),
    (fun m h => fw hP h (2176 + 4)),
    (fun m h => fw hP h (2176 + 8)),
    (fun m h => fw hP h (2176 + 12)),
    (fun m h => fw hP h (2176 + 16)),
    (fun m h => fw hP h (2176 + 20)),
    (Or.inr ⟨rfl, fun m h => fw hP h (2176 + 24), fun m h => fw hP h (2176 + 28)⟩),
    (fun m h => fw hP h 2208),
    (fun m h => fw hP h (2208 + 4)),
    (fun m h => fw hP h (2208 + 8)),
    (fun m h => fw hP h (2208 + 12)),
    (fun m h => fw hP h (2208 + 16)),
    (fun m h => fw hP h (2208 + 20)),
    (fun m h => fw hP h (2208 + 24)),
    (fun m h => fw hP h (2208 + 28)),
    (fun m h => fw hP h (2208 + 32)),
    (fun m h => fw hP h (2208 + 36)),
    (fun m h => fw hP h (2208 + 40)),
    (fun m h => fw hP h (2208 + 44)),
    (fun m h => fw hP h (2208 + 48)),
    (fun m h => fw hP h (2208 + 52)),
    (fun m h => fetch_adrp hP h (2208 + 56) ⟨by decide, by decide⟩ (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)),
    (fun m h => fw hP h (2208 + 60)),
    (fun m h => fw hP h (2208 + 64)),
    (fun m h => fw hP h (2208 + 68)),
    (fun m h => fw hP h (2208 + 72)),
    (fun m h => fetch_ldrh hP h (2208 + 76) ⟨by decide, by decide⟩ (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)),
    (fun m h => fw hP h (2208 + 80)),
    (fun m h => fw hP h (2208 + 84)),
    (fun m h => fw hP h (2208 + 88)),
    (fun m h => fw hP h (2208 + 92)),
    (fun m h => fw hP h (2208 + 96)),
    (fun m h => fw hP h (2208 + 100)),
    (fun m h => fw hP h (2208 + 104)),
    (fun m h => fw hP h (2208 + 108)),
    (fun m h => fw hP h (2208 + 112)),
    (by decide)⟩

end Poly1305DebianApi.Verify

end
end

section
section
/-! # `crypto_verify_16`, `_32` and `_64` meet `verifyNSpec`: the heap glue and the goal

`disj_rw`, `disj_rw'`, `Own`, `own_*`, `disj_own*` and `bytesIn_cell` are copied from the accepted
`Solutions/Poly1305DebianBlocks/Main.lean`; the rest is new. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianApi.Verify

open Poly1305Libsodium (bytesIn)
open Arm64 Arm64.Obj Poly1305DebianCt

/-- Two disjoint heaps do not both own a byte when one owns it read-write. -/
theorem disj_rw {h h' : Heap} (hd : h.Disjoint h') {a : BitVec 64} {b : BitVec 8} {c : HeapCell}
    (h1 : h.phys a = some (.rw b)) (h2 : h'.phys a = some c) : False := by
  rcases hd.1 a with z | z | ⟨_, z1, z2⟩
  · rw [h1] at z; cases z
  · rw [h2] at z; cases z
  · rw [h1] at z1; cases z1

theorem disj_rw' {h h' : Heap} (hd : h.Disjoint h') {a : BitVec 64} {b : BitVec 8} {c : HeapCell}
    (h1 : h.phys a = some c) (h2 : h'.phys a = some (.rw b)) : False := by
  rcases hd.1 a with z | z | ⟨_, z1, z2⟩
  · rw [h1] at z; cases z
  · rw [h2] at z; cases z
  · rw [h2] at z2; cases z2

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

theorem own_some {c : Option HeapCell} {b : BitVec 8} (h : Own c b) : ∃ c', c = some c' := by
  rcases h with h | h <;> exact ⟨_, h⟩

theorem bytesIn_cell {ro : Bool} {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap}
    (hb : (bytesIn ro a bs).holds h) (k : Nat) (hk : k < bs.length) :
    Own (h.phys (a + BitVec.ofNat 64 k)) bs[k] := by
  cases ro
  · exact Or.inl (bytes_rw bs a h hb k hk)
  · exact Or.inr (bytes_ro bs a h hb k hk)

theorem modHeap_self {h : Heap} {m : Memory} (H : ∀ a b, h.phys a = some (.rw b) → m.read8 a = b) :
    modHeap h m = h := by
  apply Heap.ext
  · funext a; simp only [modHeap]
    rcases e : h.phys a with _ | ⟨b | b | b | _ | _⟩ <;> try rfl
    simp [modCell, H a b e]
  all_goals rfl

theorem region_cell {base : BitVec 64} {len : Nat} {mm : Memory} {a : BitVec 64}
    (h : InRegion base len a) : (regionHeap base len mm).phys a = some (.rw (mm.read8 a)) := by
  simp [regionHeap, h]

/-- The data objects own `optblocker_u16` read-write, as two zero bytes. -/
theorem dataInit_ob {pl : Placement} {h : Heap}
    (hd : (libsodiumDebianOnetimeauthCtLib.dataInit pl).holds h) :
    ∀ k < 2, h.phys (pl.ρ OB + BitVec.ofNat 64 k) = some (.rw 0#8) := by
  simp only [PlacedLib.dataInit,
    show libsodiumDebianOnetimeauthCtLib.data = libsodiumDebianOnetimeauthCtData from rfl,
    libsodiumDebianOnetimeauthCtData, List.map, sepAll, Bool.false_eq_true, if_false,
    if_true] at hd
  obtain ⟨h1, h2, dA, rfl, -, hd⟩ := hd
  obtain ⟨h3, h4, dB, rfl, -, hd⟩ := hd
  obtain ⟨h5, h6, dC, rfl, -, hd⟩ := hd
  rw [show libsodiumDebianOnetimeauthCtLib.patchedData pl
      { sym := OB, align := 2, readOnly := false, bytes := libsodiumDebianOnetimeauthCtPlacedData3,
        zeroTail := 2, relocs := [] } = [0#8, 0#8] by
    simp [PlacedLib.patchedData, libsodiumDebianOnetimeauthCtPlacedData3]] at hd
  intro k hk
  have := bytes_rw [0#8, 0#8] (pl.ρ OB) h6 hd k (by simpa using hk)
  have e0 : ([0#8, 0#8] : List (BitVec 8))[k]'(by simpa using hk) = 0#8 := by
    interval_cases k <;> rfl
  rw [e0] at this
  exact cell_union_right_rw dA (cell_union_right_rw dB (cell_union_right_rw dC this))

theorem getD_lt (l : List (BitVec 8)) (j : Nat) (h : j < l.length) : l[j] = l.getD j 0#8 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem acc8_list (a b : List (BitVec 8)) (n : Nat) (ha : a.length = n) (hb : b.length = n) :
    decide (acc8 (fun j => a.getD j 0#8) (fun j => b.getD j 0#8) n = 0#8) = decide (a = b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, acc8_eq_zero]
  constructor
  · intro h
    apply List.ext_getElem (by omega)
    intro j h1 h2
    have := h j (by omega)
    rwa [← getD_lt _ _ h1, ← getD_lt _ _ h2] at this
  · rintro rfl j _; rfl

/-- `crypto_verify_n` at entry offset `E`, loop offset `L`, bound `nb = n`. -/
theorem verify_ok (name : String) (E L n : Nat) (nb : BitVec 12) (hnb : nb.toNat = n) (hn : 0 < n)
    (hsym : name ∈ libsodiumDebianOnetimeauthCtLib.text.symbols.map Prod.fst)
    (hfn : ∀ pl, libsodiumDebianOnetimeauthCtLib.fnAddr pl name = A pl E)
    (hC : ∀ pl, libsodiumDebianOnetimeauthCtLib.Placeable pl → ∀ X, Code pl X E L nb) :
    dataOk name (fun _ => verifyNSpec n) := by
  refine ⟨hsym, ?_⟩
  intro pl hP _ X _ _ _ x R s0 hpc hrun hpre hspal hCL
  obtain ⟨roX, roY, a, b⟩ := x
  change CL pl X s0.mem at hCL
  obtain ⟨H0, hH, hm⟩ := hpre
  obtain ⟨hP', hR, d1, rfl, hPre, hRh⟩ := hH
  obtain ⟨hA, hD, d2, rfl, hAh, hDh⟩ := hPre
  obtain ⟨hφ, hB, d3, rfl, ⟨rfl, hlen⟩, hBh⟩ := hAh
  obtain ⟨hX, hC', d4, rfl, hXh, hCh⟩ := hBh
  obtain ⟨hY, hF, d5, rfl, hYh, hFh⟩ := hCh
  obtain ⟨mm, rfl⟩ := hFh
  obtain ⟨hla, hlb⟩ := hlen
  set X0 := s0.readReg64 Reg.x0 with hX0
  set X1 := s0.readReg64 Reg.x1 with hX1
  -- the frame's cells, at each level
  have cF : ∀ a, W s0 a → (regionHeap (s0.sp - BitVec.ofNat 64 32) 32 mm).phys a =
      some (.rw (mm.read8 a)) := fun a w => region_cell w
  have cC : ∀ a, W s0 a → (hY.union (regionHeap (s0.sp - BitVec.ofNat 64 32) 32 mm)).phys a =
      some (.rw (mm.read8 a)) := fun a w => cell_union_right_rw d5 (cF a w)
  have cB : ∀ a, W s0 a → (hX.union (hY.union (regionHeap (s0.sp - BitVec.ofNat 64 32) 32 mm))).phys a =
      some (.rw (mm.read8 a)) := fun a w => cell_union_right_rw d4 (cC a w)
  have cA : ∀ a, W s0 a → (Heap.empty.union (hX.union (hY.union
      (regionHeap (s0.sp - BitVec.ofNat 64 32) 32 mm)))).phys a = some (.rw (mm.read8 a)) :=
    fun a w => cell_union_right_rw d3 (cB a w)
  have cH : ∀ a, W s0 a → (((Heap.empty.union (hX.union (hY.union
      (regionHeap (s0.sp - BitVec.ofNat 64 32) 32 mm)))).union hD).union hR).phys a =
      some (.rw (mm.read8 a)) := fun a w => cell_union_left (cell_union_left (cA a w))
  -- the other components avoid the frame
  have nX : ∀ a c, hX.phys a = some c → ¬ W s0 a := fun a c h w => disj_rw' d4 h (cC a w)
  have nY : ∀ a c, hY.phys a = some c → ¬ W s0 a := fun a c h w => disj_rw' d5 h (cF a w)
  have nD : ∀ a c, hD.phys a = some c → ¬ W s0 a := fun a c h w => disj_rw d2 (cA a w) h
  have nR : ∀ a c, hR.phys a = some c → ¬ W s0 a := fun a c h w =>
    disj_rw d1 (cell_union_left (cA a w)) h
  -- the entry memory
  have ok0 : MemOk s0 s0.mem := by
    refine ⟨fun _ _ => rfl, fun a w => ?_⟩
    have := hm.1 a _ (cH a w)
    exact ⟨this.2.1, this.2.2, rfl, this.2.1⟩
  have xa : ∀ j < n, Rd s0 (X0 + BitVec.ofNat 64 j) (a.getD j 0#8) := by
    intro j hj
    have c := bytesIn_cell hXh j (by omega)
    have cH' : Own ((((Heap.empty.union (hX.union (hY.union
        (regionHeap (s0.sp - BitVec.ofNat 64 32) 32 mm)))).union hD).union hR).phys
        (X0 + BitVec.ofNat 64 j)) a[j] := own_left (own_left (own_right d3 (own_left c)))
    obtain ⟨c', hc'⟩ := own_some c
    have := own_matches hm cH'
    exact ⟨nX _ _ hc', this.2.1, this.2.2, by rw [this.1, getD_lt _ _ (by omega)]⟩
  have yb : ∀ j < n, Rd s0 (X1 + BitVec.ofNat 64 j) (b.getD j 0#8) := by
    intro j hj
    have c := bytesIn_cell hYh j (by omega)
    have cH' : Own ((((Heap.empty.union (hX.union (hY.union
        (regionHeap (s0.sp - BitVec.ofNat 64 32) 32 mm)))).union hD).union hR).phys
        (X1 + BitVec.ofNat 64 j)) b[j] := own_left (own_left (own_right d3 (own_right d4 (own_left c))))
    obtain ⟨c', hc'⟩ := own_some c
    have := own_matches hm cH'
    exact ⟨nY _ _ hc', this.2.1, this.2.2, by rw [this.1, getD_lt _ _ (by omega)]⟩
  have ob : ∀ k < 2, Rd s0 (pl.ρ OB + BitVec.ofNat 64 k) 0#8 := by
    intro k hk
    have c := dataInit_ob hDh k hk
    have cH' : Own ((((Heap.empty.union (hX.union (hY.union
        (regionHeap (s0.sp - BitVec.ofNat 64 32) 32 mm)))).union hD).union hR).phys
        (pl.ρ OB + BitVec.ofNat 64 k)) 0#8 :=
      own_left (own_right d2 (Or.inl c))
    have := own_matches hm cH'
    exact ⟨nD _ _ c, this.2.1, this.2.2, this.1⟩
  have Hy : Hyp pl X s0 n (fun j => a.getD j 0#8) (fun j => b.getD j 0#8) :=
    ⟨hP, hCL, hrun, hspal, ok0, xa, yb, ob⟩
  obtain ⟨sf, hsteps, mF, ps, x0, x1, x2, x3, rfl, hok, hres⟩ :=
    run Hy (hC pl hP X) hnb hn (hpc.trans (hfn pl))
  rw [acc8_list a b n hla hlb] at hres
  refine ⟨_, hsteps, Or.inl ⟨⟨rfl, rfl, hrun⟩, ⟨rfl, ?_⟩, ?_⟩⟩
  · exact ⟨rd_hi _ _ _ _ _ _ _ _ _ _ (by decide), rd_hi _ _ _ _ _ _ _ _ _ _ (by decide),
      rd_hi _ _ _ _ _ _ _ _ _ _ (by decide), rd_hi _ _ _ _ _ _ _ _ _ _ (by decide),
      rd_hi _ _ _ _ _ _ _ _ _ _ (by decide), rd_hi _ _ _ _ _ _ _ _ _ _ (by decide),
      rd_hi _ _ _ _ _ _ _ _ _ _ (by decide), rd_hi _ _ _ _ _ _ _ _ _ _ (by decide),
      rd_hi _ _ _ _ _ _ _ _ _ _ (by decide), rd_hi _ _ _ _ _ _ _ _ _ _ (by decide),
      rd_hi _ _ _ _ _ _ _ _ _ _ (by decide), rfl⟩
  · -- the postcondition, on `modHeap` of the entry heap
    have hself : ∀ (h : Heap), (∀ a c, h.phys a = some c → ¬ W s0 a) →
        (∀ a b, h.phys a = some (.rw b) → s0.mem.read8 a = b) → modHeap h mF = h :=
      fun h hnw hv => modHeap_self fun a b e => by rw [read8_of_notW hok (hnw a _ e)]; exact hv a b e
    have vX : ∀ a b, hX.phys a = some (.rw b) → s0.mem.read8 a = b := fun a b e =>
      (hm.1 a _ (cell_union_left (cell_union_left (cell_union_right_rw d3 (cell_union_left e))))).1
    have vY : ∀ a b, hY.phys a = some (.rw b) → s0.mem.read8 a = b := fun a b e =>
      (hm.1 a _ (cell_union_left (cell_union_left (cell_union_right_rw d3
        (cell_union_right_rw d4 (cell_union_left e)))))).1
    have vD : ∀ a b, hD.phys a = some (.rw b) → s0.mem.read8 a = b := fun a b e =>
      (hm.1 a _ (cell_union_left (cell_union_right_rw d2 e))).1
    have vR : ∀ a b, hR.phys a = some (.rw b) → s0.mem.read8 a = b := fun a b e =>
      (hm.1 a _ (cell_union_right_rw d1 e)).1
    have eX := hself hX nX vX
    have eY := hself hY nY vY
    have eD := hself hD nD vD
    have eR := hself hR nR vR
    have D1 := modHeap_disjoint d1 mF
    have D2 := modHeap_disjoint d2 mF
    have D3 := modHeap_disjoint d3 mF
    have D4 := modHeap_disjoint d4 mF
    have D5 := modHeap_disjoint d5 mF
    simp only [modHeap_union, modHeap_empty, eX, eY, eD, eR, modHeap_region] at D1 D2 D3 D4 D5
    refine ⟨modHeap ((((Heap.empty.union (hX.union (hY.union
      (regionHeap (s0.sp - BitVec.ofNat 64 32) 32 mm)))).union hD).union hR)) mF, ?_,
      modHeap_matches hm hok fun a w => ⟨_, cH a w⟩⟩
    simp only [modHeap_union, modHeap_empty, eX, eY, eD, eR, modHeap_region]
    refine ⟨_, _, D1, rfl, ⟨_, _, D2, rfl, ⟨_, _, D3, rfl, ⟨rfl, ?_⟩,
      ⟨_, _, D4, rfl, hXh, ⟨_, _, D5, rfl, hYh, ⟨mF, rfl⟩⟩⟩⟩, hDh⟩, hRh⟩
    exact hres

theorem fnAddr_eq (pl : Placement) (name : String) (o : Nat)
    (h : lookup name libsodiumDebianOnetimeauthCtLib.text.symbols = some o) :
    libsodiumDebianOnetimeauthCtLib.fnAddr pl name = A pl o := by
  simp [PlacedLib.fnAddr, h]

theorem goal :
    dataOk "crypto_verify_16" (fun _ => verifyNSpec 16) ∧
      dataOk "crypto_verify_32" (fun _ => verifyNSpec 32) ∧
      dataOk "crypto_verify_64" (fun _ => verifyNSpec 64) :=
  ⟨verify_ok "crypto_verify_16" 1868 1892 16 0x010#12 rfl (by decide) (by decide)
      (fun pl => fnAddr_eq pl _ _ (by decide)) (fun pl hP X => code_16 hP X),
    verify_ok "crypto_verify_32" 2016 2048 32 0x020#12 rfl (by decide) (by decide)
      (fun pl => fnAddr_eq pl _ _ (by decide)) (fun pl hP X => code_32 hP X),
    verify_ok "crypto_verify_64" 2176 2208 64 0x040#12 rfl (by decide) (by decide)
      (fun pl => fnAddr_eq pl _ _ (by decide)) (fun pl hP X => code_64 hP X)⟩

theorem dataOk_crypto_verify_16_32_64_dev :
    dataOk "crypto_verify_16" (fun _ => verifyNSpec 16) ∧
      dataOk "crypto_verify_32" (fun _ => verifyNSpec 32) ∧
      dataOk "crypto_verify_64" (fun _ => verifyNSpec 64) :=
  goal

end Poly1305DebianApi.Verify

end
end

section
open Poly1305DebianApi

theorem solution :
    dataOk "crypto_verify_16" (fun _ => verifyNSpec 16) ∧
      dataOk "crypto_verify_32" (fun _ => verifyNSpec 32) ∧
      dataOk "crypto_verify_64" (fun _ => verifyNSpec 64) := by
  apply Poly1305DebianApi.Verify.dataOk_crypto_verify_16_32_64_dev <;> assumption

end
