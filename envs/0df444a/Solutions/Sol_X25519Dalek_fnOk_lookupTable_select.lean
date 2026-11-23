-- Prove2me | solution 1 for X25519Dalek.fnOk_lookupTable_select
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T15:31:56.547072+00:00
-- url     : https://prove2.me/submissions/9b64568e-2ecb-4a59-897f-ae1a16a6588f

import Mathlib.Tactic.IntervalCases
import Definitions.Def_X25519Dalek_Spec
import Theorems.Thm_Arm64Facts_steps_codeLoaded
import Theorems.Thm_X25519Dalek_fnOk_black_box

set_option linter.all false

section
/-! # Instruction fetch for the hook-free x25519-dalek blocks, abstract states, Reach

Fetch lemmas follow the zlib CRC-32 proofs (`ZlibCrc32.Small.Machine`), generalised to a block of
the multi-block library `x25519CliMultiLib`. -/

namespace X25519Dalek.ESel

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-- The placed program of block `i`. -/
def prog (mpl : MultiPlacement) (i : Nat) : Program := x25519CliMultiLib.blockProgram mpl i

theorem prog_base (mpl : MultiPlacement) (i : Nat) : (prog mpl i).base = mpl.base i := rfl

theorem prog_code (mpl : MultiPlacement) (i : Nat) :
    (prog mpl i).code = (x25519CliBlocks.getD i { code := [] }).patched
      (x25519CliMultiLib.blockPlacement mpl i) := rfl

theorem hook_none (mpl : MultiPlacement) (i : Nat) (pc : BitVec 64) :
    (prog mpl i).externAt? pc = none := by
  simp only [prog, Program.externAt?, Program.hookAtOff?, MultiPlacedLib.blockProgram,
    PlacedLib.program]
  have h1 : ∀ (l : List (String × Nat)) (off : Nat),
      l.findSome? (fun x => if x.2 == off then (fun _ => (none : Option (State → State))) x.1
        else none) = none := by
    intro l off; induction l with
    | nil => rfl
    | cons a l ih => simp only [List.findSome?]; split <;> simp_all
  simp

/-- Fetching without hooks. -/
def rawFetch (m : Memory) (pc : BitVec 64) : Option Instr :=
  if pc.toNat % 4 ≠ 0 then none
  else if !m.canExec pc 4 then none
  else decode (m.read32 pc)

theorem fetchMem_eq (mpl : MultiPlacement) (i : Nat) (m : Memory) (pc : BitVec 64) :
    (prog mpl i).fetchMem m pc = rawFetch m pc := by
  simp [Program.fetchMem, hook_none, rawFetch]

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

theorem patched_length (blk : CodeBlock) (pl : Placement) (h4 : blk.code.length % 4 = 0) :
    (blk.patched pl).length = blk.code.length := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE]
  rw [List.map_const', List.sum_replicate_nat, List.length_range]
  omega

theorem codeLoaded_cell {p : Program} {m : Memory} (h : p.CodeLoaded m) (i : Nat)
    (hi : i < p.code.length) :
    m.read8 (p.base + BitVec.ofNat 64 i) = p.code[i] ∧
    m.perm (p.base + BitVec.ofNat 64 i) = some Perm.rx := by
  unfold Program.CodeLoaded at h
  exact ⟨(h.2.2 i hi).1, (h.2.2 i hi).2.1⟩

theorem codeLoaded_base {p : Program} {m : Memory} (h : p.CodeLoaded m) :
    p.base.toNat % 4 = 0 ∧ p.base.toNat + p.code.length ≤ 2 ^ 64 := by
  unfold Program.CodeLoaded at h
  exact ⟨h.1, h.2.1⟩

/-- Fetch of a code word of block `i` from memory in which block `i` is loaded. -/
theorem fetch_word {mpl : MultiPlacement} {i : Nat} {blk : CodeBlock} {m : Memory}
    (hblk : x25519CliBlocks.getD i { code := [] } = blk) (h4 : blk.code.length % 4 = 0)
    (hCL : (prog mpl i).CodeLoaded m) {off : Nat} (hal : off % 4 = 0)
    (hlen : off + 4 ≤ blk.code.length) :
    rawFetch m (mpl.base i + BitVec.ofNat 64 off) =
      decode (blk.patchedWord (x25519CliMultiLib.blockPlacement mpl i) off) := by
  set pl := x25519CliMultiLib.blockPlacement mpl i
  have hcode : (prog mpl i).code = blk.patched pl := by rw [prog_code, hblk]
  have hl : (prog mpl i).code.length = blk.code.length := by rw [hcode, patched_length _ _ h4]
  obtain ⟨hb4, hnw⟩ := codeLoaded_base hCL
  rw [prog_base] at hb4 hnw
  rw [hl] at hnw
  have rd : ∀ k, k < 4 → m.read8 (mpl.base i + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      (blk.patchedWord pl off).extractLsb' (8 * k) 8 ∧
      m.perm (mpl.base i + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
    intro k hk
    have h := codeLoaded_cell hCL (off + k) (by omega)
    have ha : mpl.base i + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
        (prog mpl i).base + BitVec.ofNat 64 (off + k) := by
      rw [prog_base, BitVec.add_assoc, BitVec.ofNat_add]
    rw [ha]
    refine ⟨?_, h.2⟩
    rw [h.1]
    have ht := take4_drop_patched (blk := blk) (pl := pl) hal hlen
    have e1 : (prog mpl i).code[off + k]'(by omega) =
        (((blk.patched pl).drop off).take 4)[k]'(by
          simp [List.length_take, List.length_drop, patched_length _ _ h4]; omega) := by
      simp only [List.getElem_take, List.getElem_drop]; simp only [hcode]
    rw [e1]
    simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
    have : 8 * k + j < 32 := by omega
    simp [hj, this]; omega
  have hpc : (mpl.base i + BitVec.ofNat 64 off).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : off % 2 ^ 64 = off := Nat.mod_eq_of_lt (by omega)
    have h2 : ((mpl.base i).toNat + off) % 2 ^ 64 = (mpl.base i).toNat + off :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]; omega
  have r0 := rd 0 (by omega)
  have r1 := rd 1 (by omega)
  have r2 := rd 2 (by omega)
  have r3 := rd 3 (by omega)
  simp only [rawFetch, hpc, ne_eq, not_true_eq_false, if_false]
  generalize mpl.base i + BitVec.ofNat 64 off = a at *
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at r0 r1 r2 r3
  have hx : m.canExec a 4 = true := by
    simp only [Memory.canExec, Memory.allPerm, BitVec.add_assoc, BitVec.reduceAdd]
    simp only [BitVec.add_zero] at r0
    simp [r0.2, r1.2, r2.2, r3.2, Perm.rx]
  simp only [hx, Bool.not_true, Bool.false_eq_true, if_false]
  congr 1
  simp only [Memory.read32]
  simp only [BitVec.add_zero] at r0
  rw [show a + 0#64 = a from BitVec.add_zero a, r0.1, r1.1, r2.1, r3.1]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> rw [decide_eq_true (by omega), Bool.true_and] <;> congr 1 <;> omega

theorem patchedWord_plain (pl : Placement) (blk : CodeBlock) {off : Nat}
    (h : blk.relocAt? off = none) : blk.patchedWord pl off = blk.wordAt off := by
  simp [CodeBlock.patchedWord, h]

/-- Fetch at an unrelocated word: the decoded word of the object. -/
theorem fetch_plain {mpl : MultiPlacement} {i : Nat} {blk : CodeBlock} {m : Memory}
    (hblk : x25519CliBlocks.getD i { code := [] } = blk) (h4 : blk.code.length % 4 = 0)
    (hCL : (prog mpl i).CodeLoaded m) {off : Nat} {inst : Instr} (hal : off % 4 = 0)
    (hlen : off + 4 ≤ blk.code.length) (hr : blk.relocAt? off = none)
    (hd : decode (blk.wordAt off) = some inst) :
    rawFetch m (mpl.base i + BitVec.ofNat 64 off) = some inst := by
  rw [fetch_word hblk h4 hCL hal hlen, patchedWord_plain _ _ hr, hd]

end X25519Dalek.ESel
end

section
/-! # Abstract states, reachability and one lemma per instruction shape -/

namespace X25519Dalek.ESel

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-- The state `s` with registers `r`, stack pointer `sp`, `pc`, memory `m` and flags `ps`. -/
def mkS (s : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64) (m : Memory)
    (ps : PState) : State :=
  { s with regs := ⟨r⟩, pc := pc, sp := sp, mem := m, pstate := ps }

section lemmas
variable (s : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64) (m : Memory)
  (ps : PState)

@[simp] theorem mkS_mem : (mkS s pc r sp m ps).mem = m := rfl
@[simp] theorem mkS_pc : (mkS s pc r sp m ps).pc = pc := rfl
@[simp] theorem mkS_sp : (mkS s pc r sp m ps).sp = sp := rfl
@[simp] theorem mkS_status : (mkS s pc r sp m ps).status = s.status := rfl
@[simp] theorem mkS_pstate : (mkS s pc r sp m ps).pstate = ps := rfl
@[simp] theorem mkS_vregs : (mkS s pc r sp m ps).vregs = s.vregs := rfl
@[simp] theorem mkS_regs : (mkS s pc r sp m ps).regs = ⟨r⟩ := rfl

theorem rd_gpr (i : BitVec 5) :
    (mkS s pc r sp m ps).readReg64 (.gpr i) = if i = 31#5 then 0#64 else r i := by
  simp [State.readReg64, RegFile.read, mkS]

theorem rd_gpr' (i : BitVec 5) (hi : i ≠ 31#5) : (mkS s pc r sp m ps).readReg64 (.gpr i) = r i := by
  rw [rd_gpr, if_neg hi]

@[simp] theorem rd_xzr : (mkS s pc r sp m ps).readReg64 .xzr = 0#64 := rfl
@[simp] theorem rd_sp : (mkS s pc r sp m ps).readReg64 .sp = sp := rfl

theorem wr_gpr (i : BitVec 5) (v : BitVec 64) (hi : i ≠ 31#5) :
    (mkS s pc r sp m ps).writeReg64 (.gpr i) v = mkS s pc (Function.update r i v) sp m ps := by
  simp only [mkS, State.writeReg64, RegFile.write, beq_iff_eq, hi, if_false]
  congr 2; funext k; simp [Function.update_apply]

@[simp] theorem wr_xzr (v : BitVec 64) : (mkS s pc r sp m ps).writeReg64 .xzr v = mkS s pc r sp m ps := rfl
@[simp] theorem wr_sp (v : BitVec 64) : (mkS s pc r sp m ps).writeReg64 .sp v = mkS s pc r v m ps := rfl
@[simp] theorem mkS_advancePC : (mkS s pc r sp m ps).advancePC = mkS s (pc + 4#64) r sp m ps := rfl
@[simp] theorem mkS_setPC (q : BitVec 64) : (mkS s pc r sp m ps).setPC q = mkS s q r sp m ps := rfl
@[simp] theorem mkS_setPState (q : PState) : (mkS s pc r sp m ps).setPState q = mkS s pc r sp m q := rfl
@[simp] theorem mkS_setMem (q : Memory) : (mkS s pc r sp m ps).setMem q = mkS s pc r sp q ps := rfl

end lemmas

/-! ## Reachability -/

theorem Steps.trans' {p : Program} {a b c : State} (h1 : Steps p a b) (h2 : Steps p b c) :
    Steps p a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact Steps.step h (ih h2)

/-- From `s`, block `i`'s program reaches a state satisfying `P`. -/
def Reach (mpl : MultiPlacement) (i : Nat) (P : State → Prop) (s : State) : Prop :=
  ∃ sf, Steps (prog mpl i) s sf ∧ P sf

theorem reach_done {mpl i} {P : State → Prop} {s : State} (h : P s) : Reach mpl i P s :=
  ⟨s, Steps.refl s, h⟩

theorem reach_exec {mpl i} {P : State → Prop} {s : State} {inst : Instr}
    (hrun : s.status = .Running) (hf : rawFetch s.mem s.pc = some inst)
    (h : Reach mpl i P (execInstWithSvc (evalSvc Syscall.standard) inst s)) : Reach mpl i P s := by
  obtain ⟨sf, hs, hP⟩ := h
  refine ⟨sf, Steps.step ?_ hs, hP⟩
  have := Step.exec (prog := prog mpl i) (s := s) hrun (by rw [fetchMem_eq]; exact hf)
  exact this

end X25519Dalek.ESel
end

section
/-! # Memory: reads over writes, and the invariant that only owned writable bytes change -/

namespace X25519Dalek.ESel

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-! ## Single bytes -/

theorem read8_write8 (m : Memory) (a b : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).read8 b = if b = a then v else m.read8 b := by
  by_cases h : b = a <;> simp [Memory.write8, Memory.read8, h]

theorem perm_write8 (m : Memory) (a b : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).perm b = m.perm b := by
  by_cases h : b = a
  · subst h
    simp only [Memory.write8, Memory.perm, if_true, Memory.rawPerm]
    rcases hc : m.cells b with _ | ⟨_ | p, _⟩ <;> simp [Perm.rwx]
  · simp [Memory.write8, Memory.perm, h]

theorem lazy_write8 (m : Memory) (a b : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).isLazyFree b = if b = a then false else m.isLazyFree b := by
  by_cases h : b = a
  · subst h
    simp only [Memory.write8, Memory.isLazyFree, if_true, Memory.rawPerm]
    rcases hc : m.cells b with _ | ⟨_ | p, _⟩ <;> simp
  · simp [Memory.write8, Memory.isLazyFree, h]

theorem anon_write8 (m : Memory) (a b : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).isAnon b = m.isAnon b := by
  by_cases h : b = a
  · subst h
    simp only [Memory.write8, Memory.isAnon, if_true, Memory.rawPerm]
    rcases hc : m.cells b with _ | ⟨_ | p, _⟩ <;> simp
  · simp [Memory.write8, Memory.isAnon, h]

/-! ## The invariant: permissions kept, only bytes in `W` change -/

/-- `m` arises from `m0` by stores to bytes in `W`. -/
def MemOK (m0 : Memory) (W : BitVec 64 → Prop) (m : Memory) : Prop :=
  ∀ a, m.perm a = m0.perm a ∧ m.isLazyFree a = m0.isLazyFree a ∧ m.isAnon a = m0.isAnon a ∧
    (¬ W a → m.read8 a = m0.read8 a)

/-- The bytes of `W` are owned writable: mapped read-write and not lazily freed in `m0`. -/
def WOwned (m0 : Memory) (W : BitVec 64 → Prop) : Prop :=
  ∀ a, W a → m0.perm a = some Perm.rw ∧ m0.isLazyFree a = false

theorem memOK_refl (m0 : Memory) (W : BitVec 64 → Prop) : MemOK m0 W m0 :=
  fun _ => ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem memOK_write8 {m0 m : Memory} {W : BitVec 64 → Prop} (hW : WOwned m0 W)
    (h : MemOK m0 W m) {b : BitVec 64} (hb : W b) (v : BitVec 8) : MemOK m0 W (m.write8 b v) := by
  intro a
  obtain ⟨h1, h2, h3, h4⟩ := h a
  refine ⟨by rw [perm_write8, h1], ?_, by rw [anon_write8, h3], fun ha => ?_⟩
  · rw [lazy_write8]
    split
    · next e => subst e; rw [(hW _ hb).2]
    · exact h2
  · rw [read8_write8, if_neg (fun e => ha (by rw [e]; exact hb)), h4 ha]

/-- Fetch is unaffected by stores to non-executable owned bytes. -/
theorem rawFetch_memOK {m0 m : Memory} {W : BitVec 64 → Prop} (hW : WOwned m0 W)
    (h : MemOK m0 W m) (pc : BitVec 64) : rawFetch m pc = rawFetch m0 pc := by
  have hp : ∀ a, m.perm a = m0.perm a := fun a => (h a).1
  have hx : ∀ a, (m0.perm a).x = true → m.read8 a = m0.read8 a := by
    intro a hxa
    refine (h a).2.2.2 fun ha => ?_
    rw [(hW a ha).1] at hxa; simp [Perm.rw] at hxa
  have hce : ∀ n a, m.canExec a n = m0.canExec a n := by
    intro n; induction n with
    | zero => intro a; rfl
    | succ n ih => intro a; simp only [Memory.canExec, Memory.allPerm] at ih ⊢; rw [hp, ih]
  unfold rawFetch
  rw [hce]
  by_cases h4 : pc.toNat % 4 ≠ 0
  · rw [if_pos h4, if_pos h4]
  by_cases hex : m0.canExec pc 4 = true
  · simp only [h4, hex, if_false, Bool.not_true, Bool.false_eq_true]
    congr 1
    have hx' : ∀ k : Nat, k < 4 → (m0.perm (pc + BitVec.ofNat 64 k)).x = true := by
      intro k hk
      have : ∀ n a, m0.canExec a n = true → ∀ k < n, (m0.perm (a + BitVec.ofNat 64 k)).x = true := by
        intro n; induction n with
        | zero => intro a _ k hk; omega
        | succ n ih =>
          intro a ha k hk
          simp only [Memory.canExec, Memory.allPerm, Bool.and_eq_true] at ha
          cases k with
          | zero => simpa using ha.1
          | succ k =>
            have := ih (a + 1#64) ha.2 k (by omega)
            rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm 1 k] at this
            exact this
      exact this 4 pc hex k hk
    simp only [Memory.read32]
    have e0 := hx pc (by simpa using hx' 0 (by omega))
    have e1 := hx _ (hx' 1 (by omega))
    have e2 := hx _ (hx' 2 (by omega))
    have e3 := hx _ (hx' 3 (by omega))
    simp only [BitVec.add_zero, e0]
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, e1,
      show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, e2,
      show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, e3]
  · simp [h4, hex]

/-! ## Byte ranges -/

/-- All bytes `a + j`, `j < n`, satisfy `P`. -/
def AllB (P : BitVec 64 → Prop) (a : BitVec 64) (n : Nat) : Prop :=
  ∀ j, j < n → P (a + BitVec.ofNat 64 j)

theorem allPerm_of {m : Memory} {f : Option Perm → Bool} :
    ∀ (n : Nat) (a : BitVec 64), (∀ j, j < n → f (m.perm (a + BitVec.ofNat 64 j)) = true) →
      m.allPerm f a n = true
  | 0, _, _ => rfl
  | n + 1, a, h => by
    simp only [Memory.allPerm, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), allPerm_of n (a + 1#64) fun j hj => ?_⟩
    have := h (j + 1) (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm 1 j]
    exact this

theorem allNoLazy_of {m : Memory} :
    ∀ (n : Nat) (a : BitVec 64), (∀ j, j < n → m.isLazyFree (a + BitVec.ofNat 64 j) = false) →
      m.allNoLazyFree a n = true
  | 0, _, _ => rfl
  | n + 1, a, h => by
    simp only [Memory.allNoLazyFree, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), allNoLazy_of n (a + 1#64) fun j hj => ?_⟩
    have := h (j + 1) (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm 1 j]
    exact this

theorem canWrite_of {m0 m : Memory} {W : BitVec 64 → Prop} (hW : WOwned m0 W) (h : MemOK m0 W m)
    {a : BitVec 64} {n : Nat} (ha : AllB W a n) : m.canWrite a n = true := by
  unfold Memory.canWrite
  refine allPerm_of n a fun j hj => ?_
  rw [(h _).1, (hW _ (ha j hj)).1]; rfl

theorem canRead_of {m0 m : Memory} {W : BitVec 64 → Prop} (h : MemOK m0 W m)
    {a : BitVec 64} {n : Nat}
    (ha : AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) a n) :
    m.canRead a n = true := by
  unfold Memory.canRead
  rw [Bool.and_eq_true]
  refine ⟨allPerm_of n a fun j hj => ?_, allNoLazy_of n a fun j hj => ?_⟩
  · have := ha j hj; rw [(h _).1]; exact this.1
  · have := ha j hj; rw [(h _).2.1]; exact this.2

theorem memOK_write64 {m0 m : Memory} {W : BitVec 64 → Prop} (hW : WOwned m0 W)
    (h : MemOK m0 W m) {b : BitVec 64} (hb : AllB W b 8) (v : BitVec 64) :
    MemOK m0 W (m.write64 b v) := by
  have e : ∀ k : Nat, k < 8 → W (b + BitVec.ofNat 64 k) := hb
  unfold Memory.write64
  refine memOK_write8 hW (memOK_write8 hW (memOK_write8 hW (memOK_write8 hW (memOK_write8 hW
    (memOK_write8 hW (memOK_write8 hW (memOK_write8 hW h ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _) ?_ _)
    ?_ _
  · exact e 0 (by omega)
  · exact e 1 (by omega)
  · exact e 2 (by omega)
  · exact e 3 (by omega)
  · exact e 4 (by omega)
  · exact e 5 (by omega)
  · exact e 6 (by omega)
  · exact e 7 (by omega)

/-! ## 64-bit reads over 64-bit writes -/

theorem read64_write8_ne (m : Memory) (a b : BitVec 64) (v : BitVec 8)
    (h : ∀ k : Nat, k < 8 → b + BitVec.ofNat 64 k ≠ a) : (m.write8 a v).read64 b = m.read64 b := by
  have h0 := h 0 (by omega)
  simp only [BitVec.add_zero] at h0
  simp only [Memory.read64, read8_write8, BitVec.add_zero, if_neg h0, if_neg (h 1 (by omega)),
    if_neg (h 2 (by omega)), if_neg (h 3 (by omega)), if_neg (h 4 (by omega)),
    if_neg (h 5 (by omega)), if_neg (h 6 (by omega)), if_neg (h 7 (by omega))]

/-- Two 8-byte ranges at `a` and `b` are disjoint. -/
def Far (a b : BitVec 64) : Prop := 8 ≤ (b - a).toNat ∧ 8 ≤ (a - b).toNat

theorem ne_of_far {a b : BitVec 64} (h : Far a b) (i j : Nat) (hi : i < 8) (hj : j < 8) :
    b + BitVec.ofNat 64 j ≠ a + BitVec.ofNat 64 i := by
  intro e
  obtain ⟨h1, h2⟩ := h
  have he := congrArg BitVec.toNat e
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at he
  rw [BitVec.toNat_sub] at h1 h2
  have ha := a.isLt
  have hb := b.isLt
  rw [Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)] at he
  omega

theorem read64_write64_far (m : Memory) (a b : BitVec 64) (v : BitVec 64) (h : Far a b) :
    (m.write64 a v).read64 b = m.read64 b := by
  unfold Memory.write64
  have n := ne_of_far h
  simp only []
  rw [read64_write8_ne, read64_write8_ne, read64_write8_ne, read64_write8_ne, read64_write8_ne,
    read64_write8_ne, read64_write8_ne, read64_write8_ne]
  all_goals intro k hk
  · simpa using n 0 k (by omega) hk
  all_goals first
    | exact n 1 k (by omega) hk | exact n 2 k (by omega) hk | exact n 3 k (by omega) hk
    | exact n 4 k (by omega) hk | exact n 5 k (by omega) hk | exact n 6 k (by omega) hk
    | exact n 7 k (by omega) hk

theorem bv_add_left_cancel {a b c : BitVec 64} : a + b = a + c ↔ b = c := by
  constructor
  · intro h; have := congrArg (fun x => x - a) h; simpa using this
  · intro h; rw [h]

/-- The byte at `a + c` after a 64-bit store at `a`. -/
theorem read8_write64_off (m : Memory) (a c : BitVec 64) (v : BitVec 64) :
    (m.write64 a v).read8 (a + c) =
      if c.toNat < 8 then v.extractLsb' (8 * c.toNat) 8 else m.read8 (a + c) := by
  simp only [Memory.write64, read8_write8, bv_add_left_cancel]
  have hc : c.toNat < 2 ^ 64 := c.isLt
  by_cases h0 : c = 0#64
  · subst h0; simp
  by_cases h1 : c = 1#64
  · subst h1; simp
  by_cases h2 : c = 2#64
  · subst h2; simp
  by_cases h3 : c = 3#64
  · subst h3; simp
  by_cases h4 : c = 4#64
  · subst h4; simp
  by_cases h5 : c = 5#64
  · subst h5; simp
  by_cases h6 : c = 6#64
  · subst h6; simp
  by_cases h7 : c = 7#64
  · subst h7; simp
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, if_false]
  have : ¬ c.toNat < 8 := by
    intro hlt
    have : c.toNat = 0 ∨ c.toNat = 1 ∨ c.toNat = 2 ∨ c.toNat = 3 ∨ c.toNat = 4 ∨ c.toNat = 5 ∨
        c.toNat = 6 ∨ c.toNat = 7 := by omega
    rcases this with e | e | e | e | e | e | e | e
    all_goals first
      | exact h0 (BitVec.eq_of_toNat_eq (by simpa using e))
      | exact h1 (BitVec.eq_of_toNat_eq (by simpa using e))
      | exact h2 (BitVec.eq_of_toNat_eq (by simpa using e))
      | exact h3 (BitVec.eq_of_toNat_eq (by simpa using e))
      | exact h4 (BitVec.eq_of_toNat_eq (by simpa using e))
      | exact h5 (BitVec.eq_of_toNat_eq (by simpa using e))
      | exact h6 (BitVec.eq_of_toNat_eq (by simpa using e))
      | exact h7 (BitVec.eq_of_toNat_eq (by simpa using e))
  simp [this]

theorem concat_bytes64 (v : BitVec 64) :
    v.extractLsb' 56 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 40 8 ++ v.extractLsb' 32 8 ++
      v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> rw [decide_eq_true (by omega), Bool.true_and] <;> congr 1 <;> omega

theorem read64_write64_same (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    (m.write64 a v).read64 a = v := by
  have e := read8_write64_off m a
  unfold Memory.read64
  simp only []
  rw [show a + 0#64 = a + 0#64 from rfl, e, e, e, e, e, e, e, e]
  simpa using concat_bytes64 v

end X25519Dalek.ESel
end

section
/-! # Heaps: refreshing the read-write cells after stores, and the frame rule -/

namespace X25519Dalek.ESel

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-- Replace the byte of every read-write cell of `h` by the byte of `m`. -/
def refresh (m : Memory) (h : Heap) : Heap :=
  { h with phys := fun a => match h.phys a with
      | some (.rw _) => some (.rw (m.read8 a))
      | c => c }

theorem refresh_phys (m : Memory) (h : Heap) (a : BitVec 64) :
    (refresh m h).phys a = match h.phys a with
      | some (.rw _) => some (.rw (m.read8 a))
      | c => c := rfl

theorem refresh_union (m : Memory) (h1 h2 : Heap) :
    refresh m (h1.union h2) = (refresh m h1).union (refresh m h2) := by
  cases h1; cases h2
  simp only [refresh, Heap.union, Heap.mk.injEq, and_true]
  funext a
  rename_i p1 _ _ _ p2 _ _ _
  rcases p1 a with _ | ⟨_ | _ | _ | _ | _⟩ <;> simp

theorem refresh_disjoint {m : Memory} {h1 h2 : Heap} (hd : h1.Disjoint h2) :
    (refresh m h1).Disjoint (refresh m h2) := by
  obtain ⟨d1, d2, d3, d4, d5⟩ := hd
  refine ⟨fun a => ?_, d2, d3, d4, d5⟩
  rcases d1 a with e | e | ⟨b, e1, e2⟩
  · left; simp [refresh_phys, e]
  · right; left; simp [refresh_phys, e]
  · right; right; exact ⟨b, by simp [refresh_phys, e1], by simp [refresh_phys, e2]⟩

/-- A heap whose read-write cells already hold the bytes of `m` is unchanged by `refresh m`. -/
theorem refresh_eq_self {m : Memory} {h : Heap}
    (hc : ∀ a b, h.phys a = some (.rw b) → m.read8 a = b) : refresh m h = h := by
  cases h
  simp only [refresh, Heap.mk.injEq, and_true]
  funext a
  rename_i p _ _ _
  rcases e : p a with _ | ⟨b | _ | _ | _ | _⟩ <;> simp
  exact hc a b e

/-- Every read-write cell of `h` lies in ... ; `W` consists of read-write cells of `h`. -/
def RWDom (h : Heap) (W : BitVec 64 → Prop) : Prop := ∀ a, W a → ∃ b, h.phys a = some (.rw b)

theorem matches_refresh {h : Heap} {m0 m : Memory} {W : BitVec 64 → Prop}
    (hm : h.Matches m0) (hok : MemOK m0 W m) (hW : RWDom h W) : (refresh m h).Matches m := by
  obtain ⟨c1, c2, c3⟩ := hm
  have nw : ∀ a c, h.phys a = some c → (∀ b, c ≠ .rw b) → ¬ W a := by
    intro a c hc hne ha
    obtain ⟨b, hb⟩ := hW a ha
    rw [hc] at hb; cases hb; exact hne b rfl
  refine ⟨fun a c hc => ?_, c2, fun a ha => ?_⟩
  · obtain ⟨p1, p2, p3, p4⟩ := hok a
    rw [refresh_phys] at hc
    rcases e : h.phys a with _ | ⟨b | b | b | _ | _⟩ <;> rw [e] at hc <;> cases hc
    · have := c1 a _ e; simp only at this
      exact ⟨rfl, by rw [p1]; exact this.2.1, by rw [p2]; exact this.2.2⟩
    · have := c1 a _ e; simp only at this
      have nwa := nw a _ e (fun _ h => by cases h)
      exact ⟨by rw [p4 nwa]; exact this.1, by rw [p1]; exact this.2.1, by rw [p2]; exact this.2.2⟩
    · have := c1 a _ e; simp only at this
      have nwa := nw a _ e (fun _ h => by cases h)
      exact ⟨by rw [p4 nwa]; exact this.1, by rw [p1]; exact this.2.1, by rw [p2]; exact this.2.2⟩
    · have := c1 a _ e; simp only at this
      show m.perm a = some Perm.rw; rw [p1]; exact this
    · have := c1 a _ e; simp only at this
      show m.perm a = some Perm.protNone; rw [p1]; exact this
  · obtain ⟨p1, p2, p3, p4⟩ := hok a
    have := c3 a ha
    rw [p1, p3]; exact this

/-! ## Separation-logic basics -/

theorem empty_union (h : Heap) : Heap.empty.union h = h := by
  cases h; simp [Heap.union, Heap.empty]

theorem union_empty (h : Heap) : h.union Heap.empty = h := by
  cases h
  simp only [Heap.union, Heap.empty, Heap.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext a; split <;> simp_all
  · funext γ k; split <;> simp_all
  · funext γ k; split <;> simp_all
  · funext a; simp

theorem disjoint_empty (h : Heap) : Heap.empty.Disjoint h := by
  refine ⟨fun a => Or.inl rfl, fun γ k => Or.inl rfl, fun γ k => Or.inl rfl, ?_, fun a => Or.inl rfl⟩
  intro γ k oa v h
  rcases h with ⟨h, _⟩ | ⟨_, h⟩ <;> cases h

theorem disjoint_symm {h1 h2 : Heap} (hd : h1.Disjoint h2) : h2.Disjoint h1 := by
  obtain ⟨d1, d2, d3, d4, d5⟩ := hd
  refine ⟨fun a => ?_, fun γ k => (d2 γ k).symm, fun γ k => (d3 γ k).symm,
    fun γ k oa v h => d4 γ k oa v h.symm, fun a => (d5 a).symm⟩
  rcases d1 a with e | e | ⟨b, e1, e2⟩
  · exact Or.inr (Or.inl e)
  · exact Or.inl e
  · exact Or.inr (Or.inr ⟨b, e2, e1⟩)

theorem union_comm {h1 h2 : Heap} (hd : h1.Disjoint h2) : h1.union h2 = h2.union h1 := by
  obtain ⟨d1, d2, d3, d4, d5⟩ := hd
  cases h1; cases h2
  simp only [Heap.union, Heap.mk.injEq]
  rename_i p1 a1 f1 m1 p2 a2 f2 m2
  simp only at d1 d2 d3
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext a
    rcases d1 a with e | e | ⟨b, e1, e2⟩
    · rw [e]; rcases p2 a with _ | c <;> rfl
    · rw [e]; rcases p1 a with _ | c <;> rfl
    · rw [e1, e2]
  · funext γ k
    rcases d2 γ k with e | e
    · rw [e]; rcases a2 γ k with _ | c <;> rfl
    · rw [e]; rcases a1 γ k with _ | c <;> rfl
  · funext γ k
    rcases d3 γ k with e | e
    · rw [e]; rcases f2 γ k with _ | c <;> rfl
    · rw [e]; rcases f1 γ k with _ | c <;> rfl
  · funext a; exact Bool.or_comm _ _

theorem union_assoc (h1 h2 h3 : Heap) : (h1.union h2).union h3 = h1.union (h2.union h3) := by
  cases h1; cases h2; cases h3
  simp only [Heap.union, Heap.mk.injEq]
  rename_i p1 a1 f1 m1 p2 a2 f2 m2 p3 a3 f3 m3
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext a; rcases p1 a with _ | c <;> rfl
  · funext γ k; rcases a1 γ k with _ | c <;> rfl
  · funext γ k; rcases f1 γ k with _ | c <;> rfl
  · funext a; simp [Bool.or_assoc]

theorem disjoint_union_mpr {h1 h2 h3 : Heap} (a : h1.Disjoint h3) (b : h2.Disjoint h3) :
    (h1.union h2).Disjoint h3 := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a
  obtain ⟨b1, b2, b3, b4, b5⟩ := b
  refine ⟨fun x => ?_, fun γ k => ?_, fun γ k => ?_, fun γ k oa v hh => ?_, fun x => ?_⟩
  · simp only [Heap.union]
    rcases e : h1.phys x with _ | c
    · simpa using b1 x
    · simp only
      rcases a1 x with e' | e' | ⟨b, e1, e2⟩
      · rw [e] at e'; cases e'
      · exact Or.inr (Or.inl e')
      · rw [e] at e1; exact Or.inr (Or.inr ⟨b, e1, e2⟩)
  · simp only [Heap.union]
    rcases e : h1.auth γ k with _ | c
    · simpa using b2 γ k
    · rcases a2 γ k with e' | e'
      · rw [e] at e'; cases e'
      · exact Or.inr e'
  · simp only [Heap.union]
    rcases e : h1.frag γ k with _ | c
    · simpa using b3 γ k
    · rcases a3 γ k with e' | e'
      · rw [e] at e'; cases e'
      · exact Or.inr e'
  · simp only [Heap.union] at hh
    rcases hh with ⟨hA, hF⟩ | ⟨hA, hF⟩
    · rcases e : h1.auth γ k with _ | c <;> rw [e] at hA
      · exact b4 γ k oa v (Or.inl ⟨hA, hF⟩)
      · exact a4 γ k oa v (Or.inl ⟨by rw [e]; exact hA, hF⟩)
    · rcases e : h1.frag γ k with _ | c <;> rw [e] at hF
      · exact b4 γ k oa v (Or.inr ⟨hA, hF⟩)
      · exact a4 γ k oa v (Or.inr ⟨hA, by rw [e]; exact hF⟩)
  · simp only [Heap.union]
    rcases a5 x with e | e
    · rcases b5 x with e' | e'
      · left; simp [e, e']
      · right; exact e'
    · right; exact e

theorem disjoint_union_mp {h1 h2 h3 : Heap} (h12 : h1.Disjoint h2) (h : (h1.union h2).Disjoint h3) :
    h1.Disjoint h3 ∧ h2.Disjoint h3 := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := h12
  obtain ⟨d1, d2, d3, d4, d5⟩ := h
  simp only [Heap.union] at d1 d2 d3 d4 d5
  refine ⟨⟨fun x => ?_, fun γ k => ?_, fun γ k => ?_, fun γ k oa v hh => ?_, fun x => ?_⟩,
    ⟨fun x => ?_, fun γ k => ?_, fun γ k => ?_, fun γ k oa v hh => ?_, fun x => ?_⟩⟩
  · rcases e : h1.phys x with _ | c
    · exact Or.inl rfl
    · have := d1 x; rw [e] at this; simpa using this
  · rcases e : h1.auth γ k with _ | c
    · exact Or.inl rfl
    · have := d2 γ k; rw [e] at this; simpa using this
  · rcases e : h1.frag γ k with _ | c
    · exact Or.inl rfl
    · have := d3 γ k; rw [e] at this; simpa using this
  · rcases hh with ⟨hA, hF⟩ | ⟨hA, hF⟩
    · exact d4 γ k oa v (Or.inl ⟨by rw [hA], hF⟩)
    · exact d4 γ k oa v (Or.inr ⟨hA, by rw [hF]⟩)
  · rcases d5 x with e | e
    · left; simp only [Bool.or_eq_false_iff] at e; exact e.1
    · right; exact e
  · rcases e : h2.phys x with _ | c
    · exact Or.inl rfl
    · rcases c1 x with e1 | e1 | ⟨b, e1, e2⟩
      · have := d1 x; rw [e1, e] at this; simpa using this
      · rw [e1] at e; cases e
      · rw [e2] at e; cases e
        have := d1 x; rw [e1] at this; simpa using this
  · rcases e : h2.auth γ k with _ | c
    · exact Or.inl rfl
    · rcases c2 γ k with e1 | e1
      · have := d2 γ k; rw [e1, e] at this; simpa using this
      · rw [e1] at e; cases e
  · rcases e : h2.frag γ k with _ | c
    · exact Or.inl rfl
    · rcases c3 γ k with e1 | e1
      · have := d3 γ k; rw [e1, e] at this; simpa using this
      · rw [e1] at e; cases e
  · rcases hh with ⟨hA, hF⟩ | ⟨hA, hF⟩
    · rcases c2 γ k with e1 | e1
      · exact d4 γ k oa v (Or.inl ⟨by rw [e1]; exact hA, hF⟩)
      · rw [e1] at hA; cases hA
    · rcases c3 γ k with e1 | e1
      · exact d4 γ k oa v (Or.inr ⟨hA, by rw [e1]; exact hF⟩)
      · rw [e1] at hF; cases hF
  · rcases d5 x with e | e
    · left; simp only [Bool.or_eq_false_iff] at e; exact e.2
    · right; exact e

theorem disjoint_union_left {h1 h2 h3 : Heap} (h12 : h1.Disjoint h2) :
    (h1.union h2).Disjoint h3 ↔ h1.Disjoint h3 ∧ h2.Disjoint h3 :=
  ⟨disjoint_union_mp h12, fun h => disjoint_union_mpr h.1 h.2⟩

theorem disjoint_union_right {h1 h2 h3 : Heap} (h23 : h2.Disjoint h3) :
    h1.Disjoint (h2.union h3) ↔ h1.Disjoint h2 ∧ h1.Disjoint h3 := by
  constructor
  · intro h
    have := disjoint_union_mp h23 (disjoint_symm h)
    exact ⟨disjoint_symm this.1, disjoint_symm this.2⟩
  · intro h
    exact disjoint_symm (disjoint_union_mpr (disjoint_symm h.1) (disjoint_symm h.2))

theorem sepConj_comm (P Q : SepProp) : (P ∗ Q) = (Q ∗ P) := by
  apply SepProp.ext; funext h
  apply propext
  constructor
  · rintro ⟨h1, h2, hd, rfl, p, q⟩
    exact ⟨h2, h1, disjoint_symm hd, union_comm hd, q, p⟩
  · rintro ⟨h1, h2, hd, rfl, p, q⟩
    exact ⟨h2, h1, disjoint_symm hd, union_comm hd, q, p⟩

theorem sepConj_assoc (P Q R : SepProp) : ((P ∗ Q) ∗ R) = (P ∗ (Q ∗ R)) := by
  apply SepProp.ext; funext h
  apply propext
  constructor
  · rintro ⟨h12, h3, hd, rfl, ⟨h1, h2, hd12, rfl, p, q⟩, r⟩
    rw [disjoint_union_left hd12] at hd
    refine ⟨h1, h2.union h3, (disjoint_union_right hd.2).2 ⟨hd12, hd.1⟩, union_assoc _ _ _,
      p, h2, h3, hd.2, rfl, q, r⟩
  · rintro ⟨h1, h23, hd, rfl, p, ⟨h2, h3, hd23, rfl, q, r⟩⟩
    rw [disjoint_union_right hd23] at hd
    refine ⟨h1.union h2, h3, (disjoint_union_left hd.1).2 ⟨hd.2, hd23⟩, (union_assoc _ _ _).symm,
      ⟨h1, h2, hd.1, rfl, p, q⟩, r⟩

theorem sepConj_left_comm (P Q R : SepProp) : (P ∗ (Q ∗ R)) = (Q ∗ (P ∗ R)) := by
  rw [← sepConj_assoc, sepConj_comm P Q, sepConj_assoc]

end X25519Dalek.ESel
end

section
/-! # The frame rule for straight-line stores, and points-to facts -/

namespace X25519Dalek.ESel

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-- `P` becomes `P'` when its read-write cells are refreshed from `m`. -/
def Rf (m : Memory) (P P' : SepProp) : Prop := ∀ h, P.holds h → P'.holds (refresh m h)

/-- Every heap of `P` owns the bytes of `W` read-write. -/
def OwnsRW (P : SepProp) (W : BitVec 64 → Prop) : Prop := ∀ h, P.holds h → RWDom h W

theorem rf_sep {m : Memory} {P P' Q Q' : SepProp} (hp : Rf m P P') (hq : Rf m Q Q') :
    Rf m (P ∗ Q) (P' ∗ Q') := by
  rintro _ ⟨h1, h2, hd, rfl, p, q⟩
  exact ⟨refresh m h1, refresh m h2, refresh_disjoint hd, refresh_union m h1 h2, hp h1 p, hq h2 q⟩

theorem rf_region (m : Memory) (b : BitVec 64) (n : Nat) : Rf m (memRegion b n) (memRegion b n) := by
  rintro h ⟨mm, rfl⟩
  refine ⟨m, ?_⟩
  show refresh m (regionHeap b n mm) = regionHeap b n m
  simp only [refresh, regionHeap]
  congr 1; funext a
  split <;> simp_all

theorem rf_mono {m : Memory} {P P' P'' : SepProp} (h : Rf m P P') (h' : P' ⊢ P'') : Rf m P P'' :=
  fun k hk => h' _ (h k hk)

/-- The bytes `m.read8 (a + i)`, `i < n`. -/
def bytesAt (m : Memory) (a : BitVec 64) (n : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => m.read8 (a + BitVec.ofNat 64 i)

theorem bytesAt_length (m : Memory) (a : BitVec 64) (n : Nat) : (bytesAt m a n).length = n := by
  simp [bytesAt]

theorem bytesAt_succ (m : Memory) (a : BitVec 64) (n : Nat) :
    bytesAt m a (n + 1) = m.read8 a :: bytesAt m (a + 1#64) n := by
  simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left; intro i _
    simp only [Function.comp]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]

theorem rf_bytes (m : Memory) : ∀ (bs : List (BitVec 8)) (a : BitVec 64),
    Rf m (a ↦ₛ bs) (a ↦ₛ bytesAt m a bs.length)
  | [], a => by
    intro h hh
    simp only [pointsToBytes] at hh ⊢
    change h = Heap.empty at hh
    subst hh
    simp only [List.length_nil, bytesAt, List.range_zero, List.map_nil, pointsToBytes]
    rfl
  | b :: bs, a => by
    rw [List.length_cons, bytesAt_succ]
    simp only [pointsToBytes]
    refine rf_sep ?_ (rf_bytes m bs (a + 1#64))
    intro h hh
    change h = Heap.singleton a b at hh
    subst hh
    show refresh m (Heap.singleton a b) = Heap.singleton a (m.read8 a)
    simp only [refresh, Heap.singleton]
    congr 1; funext x
    by_cases hx : x = a <;> simp [hx]

theorem rf_ro (m : Memory) : ∀ (bs : List (BitVec 8)) (a : BitVec 64), Rf m (a ↦ᵣ bs) (a ↦ᵣ bs)
  | [], a => by
    intro h hh
    simp only [pointsToBytesRO] at hh ⊢
    change h = Heap.empty at hh
    subst hh; rfl
  | b :: bs, a => by
    simp only [pointsToBytesRO]
    refine rf_sep ?_ (rf_ro m bs (a + 1#64))
    intro h hh
    change h = Heap.singletonRO a b at hh
    subst hh
    show refresh m (Heap.singletonRO a b) = Heap.singletonRO a b
    simp only [refresh, Heap.singletonRO]
    congr 1; funext x
    by_cases hx : x = a <;> simp [hx]

/-! ## The frame theorem -/

theorem frame {m0 m : Memory} {W : BitVec 64 → Prop} {Pre Post R : SepProp}
    (hs : m0 ⊨ Pre ∗ R) (hok : MemOK m0 W m) (hW : OwnsRW Pre W) (hrf : Rf m Pre Post) :
    m ⊨ Post ∗ R := by
  obtain ⟨_, ⟨hP, hR, hd, rfl, p, r⟩, hm⟩ := hs
  have rwd : RWDom (hP.union hR) W := by
    intro a ha
    obtain ⟨b, hb⟩ := hW hP p a ha
    exact ⟨b, by simp [Heap.union, hb]⟩
  have hRe : refresh m hR = hR := by
    refine refresh_eq_self fun a b hb => ?_
    have hPn : hP.phys a = none := by
      rcases hd.1 a with e | e | ⟨b', e1, e2⟩
      · exact e
      · rw [e] at hb; cases hb
      · rw [e2] at hb; cases hb
    have hu : (hP.union hR).phys a = some (.rw b) := by simp [Heap.union, hPn, hb]
    have m0a := hm.1 a _ hu
    simp only at m0a
    have nw : ¬ W a := by
      intro ha; obtain ⟨b', hb'⟩ := hW hP p a ha; rw [hPn] at hb'; cases hb'
    rw [(hok a).2.2.2 nw, m0a.1]
  refine ⟨refresh m (hP.union hR), ⟨refresh m hP, hR, ?_, ?_, hrf hP p, r⟩,
    matches_refresh hm hok rwd⟩
  · have := refresh_disjoint (m := m) hd; rwa [hRe] at this
  · rw [refresh_union, hRe]

theorem wowned_of {m0 : Memory} {W : BitVec 64 → Prop} {Pre R : SepProp}
    (hs : m0 ⊨ Pre ∗ R) (hW : OwnsRW Pre W) : WOwned m0 W := by
  obtain ⟨_, ⟨hP, hR, hd, rfl, p, r⟩, hm⟩ := hs
  intro a ha
  obtain ⟨b, hb⟩ := hW hP p a ha
  have hu : (hP.union hR).phys a = some (.rw b) := by simp [Heap.union, hb]
  have := hm.1 a _ hu
  simp only at this
  exact ⟨this.2.1, this.2.2⟩

/-! ## Ownership facts -/

theorem ownsRW_sep_left {P Q : SepProp} {W : BitVec 64 → Prop} (h : OwnsRW P W) :
    OwnsRW (P ∗ Q) W := by
  rintro _ ⟨h1, h2, hd, rfl, p, q⟩ a ha
  obtain ⟨b, hb⟩ := h h1 p a ha
  exact ⟨b, by simp [Heap.union, hb]⟩

theorem ownsRW_sep_right {P Q : SepProp} {W : BitVec 64 → Prop} (h : OwnsRW Q W) :
    OwnsRW (P ∗ Q) W := by
  rintro _ ⟨h1, h2, hd, rfl, p, q⟩ a ha
  obtain ⟨b, hb⟩ := h h2 q a ha
  rcases hd.1 a with e | e | ⟨b', e1, e2⟩
  · exact ⟨b, by simp [Heap.union, e, hb]⟩
  · rw [e] at hb; cases hb
  · rw [e2] at hb; cases hb

theorem ownsRW_or {P : SepProp} {W1 W2 : BitVec 64 → Prop} (h1 : OwnsRW P W1) (h2 : OwnsRW P W2) :
    OwnsRW P (fun a => W1 a ∨ W2 a) := by
  intro h hp a ha
  rcases ha with ha | ha
  · exact h1 h hp a ha
  · exact h2 h hp a ha

theorem ownsRW_region (b : BitVec 64) (n : Nat) : OwnsRW (memRegion b n) (InRegion b n) := by
  rintro _ ⟨mm, rfl⟩ a ha
  exact ⟨mm.read8 a, by simp [regionHeap, ha]⟩

theorem ownsRW_bytes : ∀ (bs : List (BitVec 8)) (a : BitVec 64),
    OwnsRW (a ↦ₛ bs) (InRegion a bs.length)
  | [], a => by
    intro h _ x hx
    simp [InRegion] at hx
  | b :: bs, a => by
    simp only [pointsToBytes]
    intro h hh x hx
    by_cases e : x = a
    · subst e
      refine ownsRW_sep_left (Q := (x + 1#64) ↦ₛ bs) (W := fun y => y = x) ?_ h hh x rfl
      intro h1 p1 y hy
      change h1 = Heap.singleton x b at p1
      subst p1 hy
      exact ⟨b, by simp [Heap.singleton]⟩
    · refine ownsRW_sep_right (P := pointsTo8 a b) (ownsRW_bytes bs (a + 1#64)) h hh x ?_
      unfold InRegion at hx ⊢
      simp only [List.length_cons] at hx
      have hne : (x - a).toNat ≠ 0 := by
        intro h0; apply e; bv_omega
      have : (x - (a + 1#64)).toNat = (x - a).toNat - 1 := by bv_omega
      omega

end X25519Dalek.ESel
end

section
/-! # Execution of each instruction shape on an abstract state -/

namespace X25519Dalek.ESel

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

section exec
variable {svc : State → State} {s : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {m : Memory} {ps : PState}

theorem awc_sub (x y : BitVec 64) : (AddWithCarry64 x (~~~y) true).1 = x - y := by
  simp only [AddWithCarry64, if_true]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have hx := x.isLt; have hy := y.isLt
  omega

theorem awc_add (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
  simp only [AddWithCarry64, Bool.false_eq_true, if_false]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_add, BitVec.toNat_ofNat]
  have hx := x.isLt; have hy := y.isLt
  omega

theorem evalAddSub_sub (x y : BitVec 64) : evalAddSub .W64 .SUB x y none = (x - y, none) := by
  simp only [evalAddSub, if_true]
  rw [← awc_sub]; rfl

theorem evalAddSub_add (x y : BitVec 64) : evalAddSub .W64 .ADD x y none = (x + y, none) := by
  simp only [evalAddSub]
  rw [← awc_add]; rfl

/-- `SUB SP, SP, #imm`. -/
theorem ex_subsp (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .SUB .sp .sp imm false) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) r (sp - imm.zeroExtend 64) m ps := by
  show execAddSubImm .W64 .SUB .sp .sp imm false (mkS s pc r sp m ps) = _
  simp only [execAddSubImm, State.readReg, rd_sp, Bool.false_eq_true, if_false,
    evalAddSub_sub, State.writeReg, wr_sp, mkS_advancePC]

/-- `ADD SP, SP, #imm`. -/
theorem ex_addsp (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .ADD .sp .sp imm false) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) r (sp + imm.zeroExtend 64) m ps := by
  show execAddSubImm .W64 .ADD .sp .sp imm false (mkS s pc r sp m ps) = _
  simp only [execAddSubImm, State.readReg, rd_sp, Bool.false_eq_true, if_false,
    evalAddSub_add, State.writeReg, wr_sp, mkS_advancePC]

/-- `LDR Xd, [B, #off]`. -/
theorem ex_ldr {d : BitVec 5} {B : Reg} {bv off : BitVec 64} (hd : d ≠ 31#5)
    (hB : (mkS s pc r sp m ps).readReg64 B = bv) (hal : checkRegSPAligned (mkS s pc r sp m ps) B = true)
    (hrd : m.canRead (bv + off) 8 = true) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr d) (.Offset B off)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (m.read64 (bv + off))) sp m ps := by
  show execLdr .W64 .X64 false (.gpr d) (.Offset B off) (mkS s pc r sp m ps) = _
  simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, hB, mkS_mem, MemWidth.bytes, hrd,
    Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

/-- `STR Xt, [B, #off]`. -/
theorem ex_str {t : BitVec 5} {B : Reg} {bv off : BitVec 64} (ht : t ≠ 31#5)
    (hB : (mkS s pc r sp m ps).readReg64 B = bv) (hal : checkRegSPAligned (mkS s pc r sp m ps) B = true)
    (hw : m.canWrite (bv + off) 8 = true) :
    execInstWithSvc svc (.str .X64 (.gpr t) (.Offset B off)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) r sp (m.write64 (bv + off) (r t)) ps := by
  show execStr .X64 (.gpr t) (.Offset B off) (mkS s pc r sp m ps) = _
  simp only [execStr, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, hB, mkS_mem, MemWidth.bytes, hw,
    rd_gpr' _ _ _ _ _ _ _ ht, Memory.writeSized, mkS_setMem, mkS_advancePC]

/-- `LDP Xd1, Xd2, [B, #off]`. -/
theorem ex_ldp {d1 d2 : BitVec 5} {B : Reg} {bv off : BitVec 64} (hd1 : d1 ≠ 31#5) (hd2 : d2 ≠ 31#5)
    (hB : (mkS s pc r sp m ps).readReg64 B = bv) (hal : checkRegSPAligned (mkS s pc r sp m ps) B = true)
    (hrd1 : m.canRead (bv + off) 8 = true) (hrd2 : m.canRead (bv + off + 8#64) 8 = true) :
    execInstWithSvc svc (.ldp .W64 false (.gpr d1) (.gpr d2) (.Offset B off)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update (Function.update r d1 (m.read64 (bv + off))) d2
        (m.read64 (bv + off + 8#64))) sp m ps := by
  show execLdp .W64 false (.gpr d1) (.gpr d2) (.Offset B off) (mkS s pc r sp m ps) = _
  simp only [execLdp, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, hB, mkS_mem, MemWidth.bytes, hrd1, hrd2,
    Bool.and_self, Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ _ hd1,
    wr_gpr _ _ _ _ _ _ _ _ hd2, mkS_advancePC]

/-- `STP Xt1, Xt2, [B, #off]`. -/
theorem ex_stp {t1 t2 : BitVec 5} {B : Reg} {bv off : BitVec 64} (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5)
    (hB : (mkS s pc r sp m ps).readReg64 B = bv) (hal : checkRegSPAligned (mkS s pc r sp m ps) B = true)
    (hw1 : m.canWrite (bv + off) 8 = true) (hw2 : m.canWrite (bv + off + 8#64) 8 = true) :
    execInstWithSvc svc (.stp .W64 (.gpr t1) (.gpr t2) (.Offset B off)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) r sp ((m.write64 (bv + off) (r t1)).write64 (bv + off + 8#64) (r t2)) ps := by
  show execStp .W64 (.gpr t1) (.gpr t2) (.Offset B off) (mkS s pc r sp m ps) = _
  simp only [execStp, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, hB, mkS_mem, MemWidth.bytes, hw1, hw2,
    Bool.and_self, rd_gpr' _ _ _ _ _ _ _ ht1, rd_gpr' _ _ _ _ _ _ _ ht2, Memory.writeSized,
    mkS_setMem, mkS_advancePC]

/-- `ADD Xd, Xn, Xm, LSR #a`. -/
theorem ex_add_lsr {d n k : BitVec 5} {a : Nat} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSR a) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (r n + (r k >>> (a % 64)))) sp m ps := by
  show execAddSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSR a (mkS s pc r sp m ps) = _
  simp only [execAddSubShift, State.writeReg, State.readReg,
    rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk, shiftVal, shift64, evalAddSub_add,
    wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

/-- `AND Xd, Xn, #mask`. -/
theorem ex_andi {d n : BitVec 5} {mask : BitVec 64} (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.logicalImm .W64 .AND (.gpr d) (.gpr n) mask) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (r n &&& mask)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg, rd_gpr' _ _ _ _ _ _ _ hn, evalLogical,
    wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

/-- `MOV Wd, #imm`. -/
theorem ex_movz {d : BitVec 5} {imm : BitVec 16} (hd : d ≠ 31#5) :
    execInstWithSvc svc (.moveWide .W32 .MOVZ (.gpr d) imm 0) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (imm.zeroExtend 64)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W32 (.gpr d) _).advancePC = _
  simp only [State.writeReg, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]
  congr 2
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

/-- `MOV Xd, Xn`. -/
theorem ex_movx {d n : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W64 .ORR (.gpr d) .xzr (.gpr n) .LSL 0) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (r n)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg, rd_gpr' _ _ _ _ _ _ _ hn, rd_xzr, evalLogical,
    shiftVal, shift64, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]
  simp

/-- `RET`. -/
theorem ex_ret :
    execInstWithSvc svc (.ret (.gpr 30#5)) (mkS s pc r sp m ps) = mkS s (r 30#5) r sp m ps := by
  show State.setPC _ _ = _
  simp [rd_gpr]

end exec

end X25519Dalek.ESel
end

section
/-! # Running a block: one step at a time from an abstract state; the outcome at `RET` -/

namespace X25519Dalek.ESel

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-- One step from an abstract state at `pcb + n`, fetching from memory changed only in `W`. -/
theorem reach_mk {mpl : MultiPlacement} {i : Nat} {P : State → Prop} {s : State}
    {pcb : BitVec 64} {n : Nat} {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {m m0 : Memory}
    {ps : PState} {W : BitVec 64 → Prop} {inst : Instr}
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some inst)
    (h : Reach mpl i P (execInstWithSvc (evalSvc Syscall.standard) inst
      (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps))) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_exec (by simpa using hrun) (by rw [mkS_mem, mkS_pc, rawFetch_memOK hW hok]; exact hf) h

theorem reach_start {mpl : MultiPlacement} {i : Nat} {P : State → Prop} {s : State}
    (h : Reach mpl i P (mkS s s.pc s.regs.regs s.sp s.mem s.pstate)) : Reach mpl i P s := h

theorem pc_add4 (b : BitVec 64) (n : Nat) :
    b + BitVec.ofNat 64 n + 4#64 = b + BitVec.ofNat 64 (n + 4) := by
  rw [BitVec.add_assoc, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]

/-- `sp` is 16-byte aligned. -/
theorem spAligned_iff (s : State) : s.spAligned = true ↔ s.sp.toNat % 16 = 0 := by
  simp only [State.spAligned, beq_iff_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_and, show (0b1111#64 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod] at this
    simpa using this
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0b1111#64 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    simpa using h

theorem checkSP (s : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64)
    (m : Memory) (ps : PState) (h : sp.toNat % 16 = 0) :
    checkRegSPAligned (mkS s pc r sp m ps) .sp = true := by
  show (mkS s pc r sp m ps).spAligned = true
  rw [spAligned_iff]; exact h

theorem checkGpr (s : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64)
    (m : Memory) (ps : PState) (k : BitVec 5) :
    checkRegSPAligned (mkS s pc r sp m ps) (.gpr k) = true := rfl

theorem sp_sub_aligned {x : BitVec 64} (h : x.toNat % 16 = 0) (k : Nat) (hk : k % 16 = 0)
    (hk' : k < 2 ^ 64) : (x - BitVec.ofNat 64 k).toNat % 16 = 0 := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk']
  have := x.isLt
  omega

end X25519Dalek.ESel
end

section
/-! # Straight-line execution in SSA form

Each lemma executes one instruction from an abstract state `mkS s (pcb + n) r sp m ps` and hands
the continuation a fresh name for the value written, with its defining equation. The register
file is kept as a literal list (`regL`), so that reads and writes normalise by `simp`. -/

namespace X25519Dalek.ESel

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-- A register file given by a list of 32 values. -/
def regL (L : List (BitVec 64)) : BitVec 5 → BitVec 64 := fun k => L.getD k.toNat 0

theorem regL_update (L : List (BitVec 64)) (d : BitVec 5) (v : BitVec 64) (hL : L.length = 32) :
    Function.update (regL L) d v = regL (L.set d.toNat v) := by
  funext k
  simp only [Function.update_apply, regL, List.getD_eq_getElem?_getD]
  by_cases h : k = d
  · subst h
    have := k.isLt
    rw [if_pos rfl, List.getElem?_set_self (by omega)]; rfl
  · rw [if_neg h, List.getElem?_set_ne]
    intro e; exact h (BitVec.eq_of_toNat_eq e.symm)

theorem regL_init (r : BitVec 5 → BitVec 64) : r = regL [r 0#5, r 1#5, r 2#5, r 3#5, r 4#5, r 5#5,
    r 6#5, r 7#5, r 8#5, r 9#5, r 10#5, r 11#5, r 12#5, r 13#5, r 14#5, r 15#5, r 16#5, r 17#5,
    r 18#5, r 19#5, r 20#5, r 21#5, r 22#5, r 23#5, r 24#5, r 25#5, r 26#5, r 27#5, r 28#5, r 29#5,
    r 30#5, r 31#5] := by
  funext k
  have hk : k = BitVec.ofNat 5 k.toNat := by simp
  simp only [regL]
  generalize hj : k.toNat = j at hk
  have : j < 32 := by rw [← hj]; exact k.isLt
  subst hk
  interval_cases j <;> rfl

section ssa
variable {mpl : MultiPlacement} {i : Nat} {P : State → Prop} {s : State} {pcb : BitVec 64}
  {n : Nat} {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {m m0 : Memory} {ps : PState}
  {W : BitVec 64 → Prop}

theorem r_add_lsr {d a b : BitVec 5} {k : Nat} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.addSubShift .W64 .ADD (.gpr d) (.gpr a) (.gpr b) .LSR k))
    (h : ∀ t, t = r a + (r b >>> (k % 64)) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_add_lsr hd ha hb, pc_add4]; exact h _ rfl)

theorem r_andi {d a : BitVec 5} {mask : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.logicalImm .W64 .AND (.gpr d) (.gpr a) mask))
    (h : ∀ t, t = r a &&& mask →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_andi hd ha, pc_add4]; exact h _ rfl)

theorem r_movz {d : BitVec 5} {imm : BitVec 16} (hd : d ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.moveWide .W32 .MOVZ (.gpr d) imm 0))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r d (imm.zeroExtend 64)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_movz hd, pc_add4]; exact h)

theorem r_movx {d a : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.logicalShift .W64 .ORR (.gpr d) .xzr (.gpr a) .LSL 0))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d (r a)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_movx hd ha, pc_add4]; exact h)

theorem r_subsp {imm : BitVec 12}
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.addSubImm .W64 .SUB .sp .sp imm false))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r (sp - imm.zeroExtend 64) m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_subsp, pc_add4]; exact h)

theorem r_addsp {imm : BitVec 12}
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.addSubImm .W64 .ADD .sp .sp imm false))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r (sp + imm.zeroExtend 64) m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_addsp, pc_add4]; exact h)

theorem r_ret
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.ret (.gpr 30#5)))
    (h : P (mkS s (r 30#5) r sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_ret]; exact reach_done h)

/-! ### Loads and stores, with base `sp` (aligned) or a general register -/

theorem r_ldr_sp {d : BitVec 5} {off : BitVec 64} (hd : d ≠ 31#5) (hsp : sp.toNat % 16 = 0)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.ldr .W64 .X64 false (.gpr d) (.Offset .sp off)))
    (hrd : m.canRead (sp + off) 8 = true)
    (h : ∀ t, t = m.read64 (sp + off) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by
    rw [ex_ldr hd (rd_sp ..) (checkSP _ _ _ _ _ _ hsp) hrd, pc_add4]; exact h _ rfl)

theorem r_ldr_g {d b : BitVec 5} {off : BitVec 64} (hd : d ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.ldr .W64 .X64 false (.gpr d) (.Offset (.gpr b) off)))
    (hrd : m.canRead (r b + off) 8 = true)
    (h : ∀ t, t = m.read64 (r b + off) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by
    rw [ex_ldr hd (rd_gpr' _ _ _ _ _ _ _ hb) (checkGpr ..) hrd, pc_add4]; exact h _ rfl)

theorem r_ldp_sp {d1 d2 : BitVec 5} {off : BitVec 64} (hd1 : d1 ≠ 31#5) (hd2 : d2 ≠ 31#5)
    (hsp : sp.toNat % 16 = 0)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.ldp .W64 false (.gpr d1) (.gpr d2) (.Offset .sp off)))
    (hrd1 : m.canRead (sp + off) 8 = true) (hrd2 : m.canRead (sp + off + 8#64) 8 = true)
    (h : ∀ t1 t2, t1 = m.read64 (sp + off) → t2 = m.read64 (sp + off + 8#64) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
        (Function.update (Function.update r d1 t1) d2 t2) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by
    rw [ex_ldp hd1 hd2 (rd_sp ..) (checkSP _ _ _ _ _ _ hsp) hrd1 hrd2, pc_add4]; exact h _ _ rfl rfl)

theorem r_ldp_g {d1 d2 b : BitVec 5} {off : BitVec 64} (hd1 : d1 ≠ 31#5) (hd2 : d2 ≠ 31#5)
    (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.ldp .W64 false (.gpr d1) (.gpr d2) (.Offset (.gpr b) off)))
    (hrd1 : m.canRead (r b + off) 8 = true) (hrd2 : m.canRead (r b + off + 8#64) 8 = true)
    (h : ∀ t1 t2, t1 = m.read64 (r b + off) → t2 = m.read64 (r b + off + 8#64) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
        (Function.update (Function.update r d1 t1) d2 t2) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by
    rw [ex_ldp hd1 hd2 (rd_gpr' _ _ _ _ _ _ _ hb) (checkGpr ..) hrd1 hrd2, pc_add4]
    exact h _ _ rfl rfl)

theorem r_str_sp {t : BitVec 5} {off : BitVec 64} (ht : t ≠ 31#5) (hsp : sp.toNat % 16 = 0)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.str .X64 (.gpr t) (.Offset .sp off)))
    (hw : AllB W (sp + off) 8)
    (h : MemOK m0 W (m.write64 (sp + off) (r t)) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r sp (m.write64 (sp + off) (r t)) ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by
    rw [ex_str ht (rd_sp ..) (checkSP _ _ _ _ _ _ hsp) (canWrite_of hW hok hw), pc_add4]
    exact h (memOK_write64 hW hok hw _))

theorem r_str_g {t b : BitVec 5} {off : BitVec 64} (ht : t ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.str .X64 (.gpr t) (.Offset (.gpr b) off)))
    (hw : AllB W (r b + off) 8)
    (h : MemOK m0 W (m.write64 (r b + off) (r t)) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r sp (m.write64 (r b + off) (r t)) ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by
    rw [ex_str ht (rd_gpr' _ _ _ _ _ _ _ hb) (checkGpr ..) (canWrite_of hW hok hw), pc_add4]
    exact h (memOK_write64 hW hok hw _))

theorem r_stp_sp {t1 t2 : BitVec 5} {off : BitVec 64} (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5)
    (hsp : sp.toNat % 16 = 0)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.stp .W64 (.gpr t1) (.gpr t2) (.Offset .sp off)))
    (hw1 : AllB W (sp + off) 8) (hw2 : AllB W (sp + off + 8#64) 8)
    (h : MemOK m0 W ((m.write64 (sp + off) (r t1)).write64 (sp + off + 8#64) (r t2)) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r sp
        ((m.write64 (sp + off) (r t1)).write64 (sp + off + 8#64) (r t2)) ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  have hok1 := memOK_write64 hW hok hw1 (r t1)
  exact reach_mk hrun hW hok hf (by
    rw [ex_stp ht1 ht2 (rd_sp ..) (checkSP _ _ _ _ _ _ hsp) (canWrite_of hW hok hw1)
      (canWrite_of hW hok hw2), pc_add4]
    exact h (memOK_write64 hW hok1 hw2 _))

theorem r_stp_g {t1 t2 b : BitVec 5} {off : BitVec 64} (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5)
    (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.stp .W64 (.gpr t1) (.gpr t2) (.Offset (.gpr b) off)))
    (hw1 : AllB W (r b + off) 8) (hw2 : AllB W (r b + off + 8#64) 8)
    (h : MemOK m0 W ((m.write64 (r b + off) (r t1)).write64 (r b + off + 8#64) (r t2)) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r sp
        ((m.write64 (r b + off) (r t1)).write64 (r b + off + 8#64) (r t2)) ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  have hok1 := memOK_write64 hW hok hw1 (r t1)
  exact reach_mk hrun hW hok hf (by
    rw [ex_stp ht1 ht2 (rd_gpr' _ _ _ _ _ _ _ hb) (checkGpr ..) (canWrite_of hW hok hw1)
      (canWrite_of hW hok hw2), pc_add4]
    exact h (memOK_write64 hW hok1 hw2 _))

end ssa

/-! ## Facts used by the normalisation -/

theorem far_add_iff (b c1 c2 : BitVec 64) :
    Far (b + c1) (b + c2) ↔ 8 ≤ (c2 - c1).toNat ∧ 8 ≤ (c1 - c2).toNat := by
  unfold Far
  rw [show b + c2 - (b + c1) = c2 - c1 by bv_omega, show b + c1 - (b + c2) = c1 - c2 by bv_omega]

theorem far_add_left_iff (b c : BitVec 64) : Far (b + c) b ↔ 8 ≤ (0#64 - c).toNat ∧ 8 ≤ c.toNat := by
  unfold Far
  rw [show b - (b + c) = 0#64 - c by bv_omega, show b + c - b = c by bv_omega]

theorem far_add_right_iff (b c : BitVec 64) : Far b (b + c) ↔ 8 ≤ c.toNat ∧ 8 ≤ (0#64 - c).toNat := by
  unfold Far
  rw [show b - (b + c) = 0#64 - c by bv_omega, show b + c - b = c by bv_omega]

theorem read64_memOK {m0 m : Memory} {W : BitVec 64 → Prop} (hok : MemOK m0 W m) {x : BitVec 64}
    (hx : ∀ j : Nat, j < 8 → ¬ W (x + BitVec.ofNat 64 j)) : m.read64 x = m0.read64 x := by
  have e := fun j hj => (hok (x + BitVec.ofNat 64 j)).2.2.2 (hx j hj)
  simp only [Memory.read64]
  have e0 := e 0 (by omega)
  simp only [BitVec.add_zero] at e0
  rw [BitVec.add_zero, e0, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, e 1 (by omega),
    show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, e 2 (by omega),
    show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, e 3 (by omega),
    show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, e 4 (by omega),
    show (5#64 : BitVec 64) = BitVec.ofNat 64 5 from rfl, e 5 (by omega),
    show (6#64 : BitVec 64) = BitVec.ofNat 64 6 from rfl, e 6 (by omega),
    show (7#64 : BitVec 64) = BitVec.ofNat 64 7 from rfl, e 7 (by omega)]

end X25519Dalek.ESel
end

section
/-! # Buffers: byte cells of points-to assertions, 64-bit words of byte lists -/

namespace X25519Dalek.ESel

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

theorem cell_sep_left {P Q : SepProp} {h : Heap} (hs : (P ∗ Q).holds h) {x : BitVec 64} {c : HeapCell}
    (hc : ∀ h1, P.holds h1 → h1.phys x = some c) : h.phys x = some c := by
  obtain ⟨h1, h2, _, rfl, p, _⟩ := hs
  simp [Heap.union, hc h1 p]

theorem cell_sep_right {P Q : SepProp} {h : Heap} (hs : (P ∗ Q).holds h) {x : BitVec 64}
    {c : HeapCell} (hc : ∀ h2, Q.holds h2 → h2.phys x = some c) : h.phys x = some c := by
  obtain ⟨h1, h2, hd, rfl, _, q⟩ := hs
  have e := hc h2 q
  rcases hd.1 x with e1 | e1 | ⟨b, e1, e2⟩
  · simp [Heap.union, e1, e]
  · rw [e1] at e; cases e
  · rw [e2] at e; simp only [Option.some.injEq] at e; subst e; simp [Heap.union, e1]

theorem rwCells_bytes : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap), (a ↦ₛ bs).holds h →
    ∀ i (hi : i < bs.length), h.phys (a + BitVec.ofNat 64 i) = some (.rw bs[i])
  | [], _, _, _, i, hi => by simp at hi
  | b :: bs, a, h, hh, i, hi => by
    simp only [pointsToBytes] at hh
    cases i with
    | zero =>
      refine cell_sep_left hh fun h1 p1 => ?_
      change h1 = Heap.singleton a b at p1
      subst p1; simp [Heap.singleton]
    | succ i =>
      refine cell_sep_right hh fun h2 p2 => ?_
      have := rwCells_bytes bs (a + 1#64) h2 p2 i (by simp at hi; omega)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm 1 i] at this
      simpa using this

theorem roCells_bytes : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap), (a ↦ᵣ bs).holds h →
    ∀ i (hi : i < bs.length), h.phys (a + BitVec.ofNat 64 i) = some (.ro bs[i])
  | [], _, _, _, i, hi => by simp at hi
  | b :: bs, a, h, hh, i, hi => by
    simp only [pointsToBytesRO] at hh
    cases i with
    | zero =>
      refine cell_sep_left hh fun h1 p1 => ?_
      change h1 = Heap.singletonRO a b at p1
      subst p1; simp [Heap.singletonRO]
    | succ i =>
      refine cell_sep_right hh fun h2 p2 => ?_
      have := roCells_bytes bs (a + 1#64) h2 p2 i (by simp at hi; omega)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm 1 i] at this
      simpa using this

/-! ## 64-bit words of byte lists -/

theorem readLE8_eq (bs : List (BitVec 8)) (off : Nat) :
    ByteSlice.readLE bs off 8 = bs.getD (off + 7) 0#8 ++ bs.getD (off + 6) 0#8 ++
      bs.getD (off + 5) 0#8 ++ bs.getD (off + 4) 0#8 ++ bs.getD (off + 3) 0#8 ++
      bs.getD (off + 2) 0#8 ++ bs.getD (off + 1) 0#8 ++ bs.getD (off + 0) 0#8 := by
  simp only [ByteSlice.readLE]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append,
    BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero]
  simp only [Nat.sub_sub, Nat.reduceAdd, Nat.reduceMul, Nat.sub_zero, Bool.false_or]
  split_ifs <;> simp (disch := omega) only [decide_eq_true, decide_eq_false, BitVec.getLsbD_of_ge,
    Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_or, Bool.or_false,
    Bool.not_true, Bool.not_false]

theorem read64_eq_readLE (m : Memory) (x : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (h : ∀ j, j < 8 → m.read8 (x + BitVec.ofNat 64 j) = bs.getD (off + j) 0#8) :
    m.read64 x = ByteSlice.readLE bs off 8 := by
  rw [readLE8_eq]
  simp only [Memory.read64]
  rw [show x + 0#64 = x + BitVec.ofNat 64 0 from rfl, h 0 (by omega),
    show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, h 1 (by omega),
    show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, h 2 (by omega),
    show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, h 3 (by omega),
    show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, h 4 (by omega),
    show (5#64 : BitVec 64) = BitVec.ofNat 64 5 from rfl, h 5 (by omega),
    show (6#64 : BitVec 64) = BitVec.ofNat 64 6 from rfl, h 6 (by omega),
    show (7#64 : BitVec 64) = BitVec.ofNat 64 7 from rfl, h 7 (by omega)]

theorem bytesAt_getD (m : Memory) (x : BitVec 64) (n k : Nat) (hk : k < n) :
    (bytesAt m x n).getD k 0#8 = m.read8 (x + BitVec.ofNat 64 k) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hk]

theorem readLE_bytesAt (m : Memory) (x : BitVec 64) (n off : Nat) (h : off + 8 ≤ n) :
    ByteSlice.readLE (bytesAt m x n) off 8 = m.read64 (x + BitVec.ofNat 64 off) := by
  symm
  apply read64_eq_readLE
  intro j hj
  rw [bytesAt_getD _ _ _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The word at `a + off` of a buffer whose bytes are unchanged in `m`. -/
theorem read64_buf {m0 m : Memory} {W : BitVec 64 → Prop} {a : BitVec 64} {bs : List (BitVec 8)}
    (hb : ∀ i (hi : i < bs.length), m0.read8 (a + BitVec.ofNat 64 i) = bs[i] ∧
      (m0.perm (a + BitVec.ofNat 64 i)).r = true ∧ m0.isLazyFree (a + BitVec.ofNat 64 i) = false ∧
      ¬ W (a + BitVec.ofNat 64 i))
    (hok : MemOK m0 W m) (off : Nat) (hoff : off + 8 ≤ bs.length) :
    m.read64 (a + BitVec.ofNat 64 off) = ByteSlice.readLE bs off 8 := by
  apply read64_eq_readLE
  intro j hj
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have := hb (off + j) (by omega)
  rw [(hok _).2.2.2 this.2.2.2, this.1, List.getD_eq_getElem?_getD]
  simp [List.getElem?_eq_getElem (show off + j < bs.length by omega)]

theorem canRead_buf {m0 m : Memory} {W : BitVec 64 → Prop} {a : BitVec 64} {bs : List (BitVec 8)}
    (hb : ∀ i (hi : i < bs.length), m0.read8 (a + BitVec.ofNat 64 i) = bs[i] ∧
      (m0.perm (a + BitVec.ofNat 64 i)).r = true ∧ m0.isLazyFree (a + BitVec.ofNat 64 i) = false ∧
      ¬ W (a + BitVec.ofNat 64 i))
    (hok : MemOK m0 W m) (off : Nat) (hoff : off + 8 ≤ bs.length) :
    m.canRead (a + BitVec.ofNat 64 off) 8 = true := by
  refine canRead_of hok fun j hj => ?_
  show (m0.perm _).r = true ∧ _
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have := hb (off + j) (by omega)
  exact ⟨this.2.1, this.2.2.1⟩

end X25519Dalek.ESel
end

section
/-! # Decoding a relocated cross-block `BL`

`decode_branchWord_bl` and the relocation bookkeeping of `fetch_bl` are copied from
`Solutions/X25519DalekField/G/Reloc.lean` (sibling batch q447-xd-goal, after the zlib CRC-32
mission's `ZlibCrc32.Small.RelocBase`); the fetch is restated for the EF framework (`rawFetch`
from memory in which block `i` is loaded). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.ESel

open Arm64 Arm64.Obj

theorem beq_false_of_mask {w K A M C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A &&& M) :
    (w &&& M == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, ← hK, BitVec.and_assoc, BitVec.and_comm M K, ← BitVec.and_assoc]

theorem beq_false_of_mask' {w K A C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A) :
    (w == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, hK]

theorem decode_b_class (w : BitVec 32) (hK : w &&& 0x7c000000#32 = 0x14000000#32) :
    decode w = some (if w.getLsbD 31 then .bl (((w.extractLsb' 0 26).signExtend 64) <<< 2)
      else .b (((w.extractLsb' 0 26).signExtend 64) <<< 2)) := by
  delta decode
  simp only [beq_false_of_mask' hK (C := 0xd503201f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4000001#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4200000#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd503201f#32) (M := 0xfffff01f#32) (by decide),
    beq_false_of_mask hK (C := 0#32) (M := 0xffff0000#32) (by decide),
    beq_false_of_mask hK (C := 0xd50b7420#32) (M := 0xffffffe0#32) (by decide),
    beq_false_of_mask hK (C := 0x10000000#32) (M := 0x1f000000#32) (by decide),
    beq_false_of_mask hK (C := 0x11000000#32) (M := 0x1f800000#32) (by decide),
    beq_false_of_mask hK (C := 0x12000000#32) (M := 0x1f800000#32) (by decide),
    beq_false_of_mask hK (C := 0x12800000#32) (M := 0x1f800000#32) (by decide),
    beq_false_of_mask hK (C := 0x13000000#32) (M := 0x1f800000#32) (by decide),
    beq_false_of_mask hK (C := 0x13800000#32) (M := 0x7f800000#32) (by decide), hK]
  cases h : w.getLsbD 31 <;> simp [h]

theorem hi_bits27 (D : BitVec 64) (h1 : -(2^27:Int) ≤ D.toInt) (h2 : D.toInt < 2^27) :
    ∀ i, 27 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 27 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  have hc : D.toNat < 2 ^ 27 ∨ 2 ^ 64 - 2 ^ 27 ≤ D.toNat := by split at h1 <;> omega
  rcases hc with h | h
  · have e : ∀ j, 27 ≤ j → D.getLsbD j = false := fun j hj =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hj))
    rw [e i hi1, e 27 le_rfl]
  · have hn : (~~~D).toNat < 2 ^ 27 := by rw [BitVec.toNat_not]; omega
    have e : ∀ j, 27 ≤ j → j < 64 → D.getLsbD j = true := fun j hj hj2 => by
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) hj))
      have h' : (~~~D).getLsbD j = false := this
      rw [BitVec.getLsbD_not] at h'
      simpa [hj2] using h'
    rw [e i hi1 hi2, e 27 le_rfl (by norm_num)]

theorem lo_bits2 (D : BitVec 64) (h : D.toNat % 4 = 0) : ∀ i, i < 2 → D.getLsbD i = false := by
  intro i hi
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  generalize D.toNat = n at h ⊢
  interval_cases i <;> simp <;> omega

/-- A relocated `BL` (template `0x94000000`) calls its target. -/
theorem decode_branchWord_bl {P T : BitVec 64} (hr : BranchInRange P T) :
    decode (branchWord 0x94000000#32 P T) = some (.bl (T - P)) := by
  have hm : ((0x94000000#32 &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32))
      &&& 0x7c000000#32 = 0x14000000#32 := by
    simp only [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.reduceAnd, BitVec.and_zero,
      BitVec.or_zero]
  have h31 : ((0x94000000#32 &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32)).getLsbD 31
      = true := by simp
  have hoff : ((((0x94000000#32 &&& 0xfc000000#32) ||| (((T - P) >>> 2).setWidth 32 &&& 0x03ffffff#32)).extractLsb' 0 26).signExtend 64)
      <<< 2 = T - P := by
    have hlo := lo_bits2 _ hr.1
    have hhi := hi_bits27 _ hr.2.1 hr.2.2
    have c1 : ∀ k, k < 26 → (0x03ffffff#32).getLsbD k = true := by decide
    have c2 : ∀ k, k < 26 → ((0x94000000#32).getLsbD k && (0xfc000000#32).getLsbD k) = false := by
      decide
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb',
      BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
      BitVec.msb_eq_getLsbD_last]
    rcases (by omega : i < 2 ∨ (2 ≤ i ∧ i < 28) ∨ 28 ≤ i) with h | ⟨h1, h2⟩ | h
    · rw [hlo i h]; simp [h]
    · rw [if_pos (by omega), Nat.zero_add, show 2 + (i - 2) = i by omega, c1 _ (by omega),
        c2 _ (by omega)]
      simp [hi, show i - 2 < 64 by omega, show i - 2 < 26 by omega, show i - 2 < 32 by omega,
        show ¬ i < 2 by omega]
    · rw [if_neg (by omega), hhi i (by omega) hi]
      simp only [Nat.reduceSub, Nat.zero_add, Nat.reduceAdd, c1 25 (by omega), c2 25 (by omega)]
      simp [hi, show ¬ i < 2 by omega, show i - 2 < 64 by omega]
  rw [branchWord, decode_b_class _ hm, h31, if_pos rfl, hoff]

theorem blk_placeable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {i : Nat}
    (hi : i < 19) :
    (x25519CliBlocks.getD i { code := [] }).Placeable (x25519CliMultiLib.blockPlacement mpl i) := by
  have := hP.blocks_ok i (by exact hi)
  show (x25519CliMultiLib.blocks.getD i { code := [] }).Placeable _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by exact hi)]
  exact this

/-- The `BL callee` at offset `off` of block `i` (a `call26` relocation to the first symbol of
block `j`, which is not a symbol of block `i`): fetched as `bl (base j - (base i + off))`. -/
theorem fetch_bl {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m : Memory}
    {i j off : Nat} (hi : i < 19) {b : CodeBlock} (hb : x25519CliBlocks.getD i { code := [] } = b)
    (hCL : (prog mpl i).CodeLoaded m) (sym : String)
    (hal : off % 4 = 0 ∧ off + 4 ≤ b.code.length) (h4 : b.code.length % 4 = 0)
    (hr : b.relocAt? off = some { off := off, kind := .call26, sym := sym })
    (hmem : ({ off := off, kind := .call26, sym := sym } : RelocEntry) ∈ b.relocs)
    (hw : b.wordAt off = 0x94000000#32)
    (hlk : lookup sym b.symbols = none)
    (hlj : lookupBlockSym sym x25519CliMultiLib.blocks = some (j, 0))
    (hrel1 : b.relaxableAt off = false) (hrel2 : 4 ≤ off → b.relaxableAt (off - 4) = false)
    (hwk : b.weakRefs = []) :
    rawFetch m (mpl.base i + BitVec.ofNat 64 off) =
      some (.bl (mpl.base j + BitVec.ofNat 64 0 - (mpl.base i + BitVec.ofNat 64 off))) := by
  rw [fetch_word hb h4 hCL hal.1 hal.2]
  have hres : x25519CliMultiLib.resolve mpl sym = mpl.base j + BitVec.ofNat 64 0 := by
    simp only [MultiPlacedLib.resolve, hlj]
  have hb2b : b.b2bNext? { off := off, kind := .call26, sym := sym } = none := by
    rw [CodeBlock.b2bNext?]; simp only [hlk]; simp
  have htg : b.target (x25519CliMultiLib.blockPlacement mpl i)
      { off := off, kind := .call26, sym := sym } = mpl.base j + BitVec.ofNat 64 0 := by
    rw [CodeBlock.target, CodeBlock.resolve]; simp only [hlk]
    simp [addSignedAddr, MultiPlacedLib.blockPlacement, hres]
  have hT : b.relocTarget (x25519CliMultiLib.blockPlacement mpl i) off
      { off := off, kind := .call26, sym := sym } = mpl.base j + BitVec.ofNat 64 0 := by
    rw [CodeBlock.relocTarget, hb2b]
    split <;> simp_all
  have hpl : b.Placeable (x25519CliMultiLib.blockPlacement mpl i) := hb ▸ blk_placeable hP hi
  have hrange : BranchInRange (mpl.base i + BitVec.ofNat 64 off) (mpl.base j + BitVec.ofNat 64 0) := by
    have h := (hpl.relocs_ok _ hmem).2.2
    rw [hT] at h
    exact h
  have hpw : b.patchedWord (x25519CliMultiLib.blockPlacement mpl i) off =
      branchWord 0x94000000#32 (mpl.base i + BitVec.ofNat 64 off) (mpl.base j + BitVec.ofNat 64 0) := by
    have hbase : (x25519CliMultiLib.blockPlacement mpl i).base = mpl.base i := rfl
    have hr1 : b.relaxedAt (x25519CliMultiLib.blockPlacement mpl i) off = false := by
      simp [CodeBlock.relaxedAt, hrel1]
    have hr2 : (decide (4 ≤ off) && b.relaxedAt (x25519CliMultiLib.blockPlacement mpl i) (off - 4)) = false := by
      by_cases h4 : 4 ≤ off
      · simp [CodeBlock.relaxedAt, hrel2 h4]
      · simp [h4]
    have hu : b.undefWeakBranch (x25519CliMultiLib.blockPlacement mpl i)
        { off := off, kind := .call26, sym := sym } = false := by
      simp [CodeBlock.undefWeakBranch, hwk]
    rw [CodeBlock.patchedWord]
    simp only [hr, hr1, hr2, hw, hbase, hu, hT, Bool.false_eq_true, if_false]
    simp [RelocKind.isGotOrTlsIe, patchRelocWord]
  rw [hpw, decode_branchWord_bl hrange]

theorem blk06 : x25519CliBlocks.getD 6 { code := [] } = x25519CliBlk06 := rfl

theorem bb_lookup : lookupBlockSym "subtle::black_box::<u8>" x25519CliMultiLib.blocks = some (0, 0) := by
  decide +kernel

section
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m : Memory}
  (hCL : (prog mpl 6).CodeLoaded m)
include hP hCL

theorem f06_132 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 132) =
    some (.bl (mpl.base 0 + BitVec.ofNat 64 0 - (mpl.base 6 + BitVec.ofNat 64 132))) :=
  fetch_bl hP (by decide) blk06 hCL "subtle::black_box::<u8>" ⟨by decide, by decide⟩ (by decide) rfl
    (by decide) (by decide +kernel) (by decide) bb_lookup (by decide) (fun _ => by decide) rfl

theorem f06_432 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 432) =
    some (.bl (mpl.base 0 + BitVec.ofNat 64 0 - (mpl.base 6 + BitVec.ofNat 64 432))) :=
  fetch_bl hP (by decide) blk06 hCL "subtle::black_box::<u8>" ⟨by decide, by decide⟩ (by decide) rfl
    (by decide) (by decide +kernel) (by decide) bb_lookup (by decide) (fun _ => by decide) rfl

end

end X25519Dalek.ESel
end

section
/-! # Calling `subtle::black_box::<u8>` (block 0) from block 6 through its published contract

The `BL` (relocated to block 0), the callee's `fnOk` contract with the caller's frame `F`, and the
return; after the pattern of `call_mul` in `Solutions/X25519DalekField/G/P22Call.lean`. The code
stays loaded across the call by the published `Arm64Facts.steps_codeLoaded`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.ESel

open Arm64 Arm64.Obj

theorem step_transfer {p q : Program} (hp : ∀ pc, p.externAt? pc = none)
    (hq : ∀ pc, q.externAt? pc = none) (hs : p.svc = q.svc) {s s' : State}
    (h : Step p s s') : Step q s s' := by
  have hf : ∀ m pc, p.fetchMem m pc = q.fetchMem m pc := by
    intro m pc; simp only [Program.fetchMem, hp, hq]
  cases h with
  | exec hrun hfe =>
    have := Step.exec (prog := q) hrun (by rw [← hf]; exact hfe)
    simpa only [Program.evalInst, hs] using this
  | halt_unmapped hrun hfe _ =>
    exact Step.halt_unmapped hrun (by rw [← hf]; exact hfe) (hq _)
  | externHook _ he _ _ => rw [hp] at he; cases he
  | extern_fault _ he _ => rw [hp] at he; cases he

theorem steps_transfer {p q : Program} (hp : ∀ pc, p.externAt? pc = none)
    (hq : ∀ pc, q.externAt? pc = none) (hs : p.svc = q.svc) {s s' : State}
    (h : Steps p s s') : Steps q s s' := by
  induction h with
  | refl => exact Steps.refl _
  | step h1 _ ih => exact Steps.step (step_transfer hp hq hs h1) ih

theorem sat_false {m : Memory} {F : SepProp} (h : m ⊨ ⌜False⌝ ∗ F) : False := by
  obtain ⟨_, ⟨h1, h2, _, rfl, ⟨_, hf⟩, _⟩, _⟩ := h
  exact hf

theorem ex_bl {svc : State → State} {s : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {m : Memory} {ps : PState} (off : BitVec 64) :
    execInstWithSvc svc (.bl off) (mkS s pc r sp m ps) =
      mkS s (pc + off) (Function.update r 30#5 (pc + 4#64)) sp m ps := by
  show State.setPC (State.writeReg64 _ _ _) _ = _
  rw [show Reg.lr = Reg.gpr 30#5 from rfl, wr_gpr _ _ _ _ _ _ _ _ (by decide), mkS_setPC]
  rfl

theorem sat_pure_sep_iff {m : Memory} {φ : Prop} {P : SepProp} : (m ⊨ ⌜φ⌝ ∗ P) ↔ φ ∧ (m ⊨ P) := by
  constructor
  · rintro ⟨_, ⟨h1, h2, _, rfl, ⟨rfl, hφ⟩, hp⟩, hm⟩
    refine ⟨hφ, _, hp, ?_⟩
    rwa [empty_union] at hm
  · rintro ⟨hφ, h, hp, hm⟩
    exact ⟨h, ⟨Heap.empty, h, disjoint_empty h, (empty_union h).symm, ⟨rfl, hφ⟩, hp⟩, hm⟩

/-- A call to `black_box` from block 6 at offset `off`, with the caller's frame `F`. -/
theorem call_bb {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    {Q : State → Prop} {sb : State} {off : Nat}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {m : Memory} {ps : PState} {F : SepProp}
    (hrun : sb.status = .Running) (hCL : x25519CliMultiLib.CodeLoaded mpl m)
    (hf : rawFetch m (mpl.base 6 + BitVec.ofNat 64 off) =
      some (.bl (mpl.base 0 + BitVec.ofNat 64 0 - (mpl.base 6 + BitVec.ofNat 64 off))))
    (hal : sp.toNat % 16 = 0)
    (hmem : m ⊨ memRegion (sp - 16#64) 16 ∗ F)
    (hcont : ∀ sf : State, sf.status = .Running → sf.pc = mpl.base 6 + BitVec.ofNat 64 (off + 4) →
      sf.sp = sp → (∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 30 → sf.regs.regs k = r k) →
      calleeSavedVRegs sf = calleeSavedVRegs sb → x25519CliMultiLib.CodeLoaded mpl sf.mem →
      (sf.mem ⊨ memRegion (sp - 16#64) 16 ∗ F) →
      (sf.regs.regs 0#5).truncate 8 = (r 0#5).truncate 8 →
      Reach mpl 6 Q sf) :
    Reach mpl 6 Q (mkS sb (mpl.base 6 + BitVec.ofNat 64 off) r sp m ps) := by
  refine reach_exec (by simpa using hrun) (by rw [mkS_mem, mkS_pc]; exact hf) ?_
  rw [ex_bl]
  have epc : mpl.base 6 + BitVec.ofNat 64 off + (mpl.base 0 + BitVec.ofNat 64 0 -
      (mpl.base 6 + BitVec.ofNat 64 off)) = mpl.base 0 + BitVec.ofNat 64 0 := by abel
  rw [epc]
  obtain ⟨i1, o1, hlk1, hsub⟩ := X25519Dalek.fnOk_black_box
  rw [bb_lookup] at hlk1
  obtain ⟨rfl, rfl⟩ : 0 = i1 ∧ 0 = o1 := by simpa using hlk1
  have hfa : x25519CliMultiLib.fnAddr mpl "subtle::black_box::<u8>" = mpl.base 0 + BitVec.ofNat 64 0 := by
    simp only [MultiPlacedLib.fnAddr, bb_lookup]
  set s1 := mkS sb (mpl.base 0 + BitVec.ofNat 64 0)
    (Function.update r 30#5 (mpl.base 6 + BitVec.ofNat 64 off + 4#64)) sp m ps with hs1
  have e0 : BitVec.truncate 8 (s1.readReg32 Reg.x0) = (r 0#5).truncate 8 := by
    simp only [hs1, State.readReg32, Reg.x0, rd_gpr' _ _ _ _ _ _ _ (show (0#5 : BitVec 5) ≠ 31#5 by decide)]
    rw [Function.update_of_ne (by decide)]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [hi, show i < 32 by omega]
  have hpre : s1.mem ⊨ (x25519CliMultiLib.withCodeLoaded mpl
      (ToBaseSpec.toSpec ((fun _ => blackBoxU8Spec) mpl) (mpl.base 0))).pre ((r 0#5).truncate 8) s1 ∗ F := by
    show m ⊨ ((⌜BitVec.truncate 8 (s1.readReg32 Reg.x0) = (r 0#5).truncate 8⌝ ∗
        memRegion (sp - BitVec.ofNat 64 16) 16) ∗ ⌜x25519CliMultiLib.CodeLoaded mpl m⌝) ∗ F
    rw [sepConj_comm (_ ∗ _) ⌜_⌝, sepConj_assoc, sat_pure_sep_iff, sepConj_assoc, sat_pure_sep_iff]
    exact ⟨hCL, e0, hmem⟩
  obtain ⟨sf, hsteps, hout⟩ := hsub mpl hP ((r 0#5).truncate 8) F s1 (by simp [hs1, hfa]) hrun hpre
    ((spAligned_iff _).2 (by simpa [hs1] using hal))
    (hCL 0 (by decide))
  have hst6 : Steps (prog mpl 6) s1 sf := steps_transfer (hook_none mpl 0) (hook_none mpl 6) rfl hsteps
  rcases hout with ⟨⟨hpcf, hspf, hrunf⟩, ⟨_, hcs⟩, hpost⟩ | ⟨_, hpan⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  rotate_left
  · exact (sat_false hpan).elim
  · exact (sat_false hex).elim
  · exact (sat_false hoom).elim
  have hpc' : sf.pc = mpl.base 6 + BitVec.ofNat 64 (off + 4) := by
    rw [hpcf]; simp [hs1, rd_gpr, Reg.lr, BitVec.add_assoc, BitVec.ofNat_add]
  have hsp' : sf.sp = sp := by rw [hspf]; rfl
  have hCLf : x25519CliMultiLib.CodeLoaded mpl sf.mem := fun i hi =>
    Arm64Facts.steps_codeLoaded hsteps (hCL i hi)
  simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, blackBoxU8Spec, stackFrame, hsp'] at hpost
  rw [sepConj_assoc, sepConj_comm (memRegion _ _) _, sepConj_assoc, sat_pure_sep_iff] at hpost
  obtain ⟨hv, hpost⟩ := hpost
  have hkept : ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 30 → sf.regs.regs k = r k := by
    intro k hk1 hk2
    obtain ⟨a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, -⟩ := hcs
    have hk : k = BitVec.ofNat 5 k.toNat := by simp
    generalize hj : k.toNat = j at hk hk1 hk2
    subst hk
    have key : ∀ i : BitVec 5, i ≠ 31#5 → i ≠ 30#5 → sf.readReg64 (.gpr i) = s1.readReg64 (.gpr i) →
        sf.regs.regs i = r i := by
      intro i h31 h30 h
      rw [hs1, rd_gpr' _ _ _ _ _ _ _ h31, Function.update_of_ne h30] at h
      rw [← h]; simp [State.readReg64, RegFile.read, h31]
    simp only [Reg.fp] at a29
    interval_cases j
    all_goals first
      | exact key _ (by decide) (by decide) a19 | exact key _ (by decide) (by decide) a20
      | exact key _ (by decide) (by decide) a21 | exact key _ (by decide) (by decide) a22
      | exact key _ (by decide) (by decide) a23 | exact key _ (by decide) (by decide) a24
      | exact key _ (by decide) (by decide) a25 | exact key _ (by decide) (by decide) a26
      | exact key _ (by decide) (by decide) a27 | exact key _ (by decide) (by decide) a28
      | exact key _ (by decide) (by decide) a29
  have hvr : calleeSavedVRegs sf = calleeSavedVRegs sb := by rw [hcs.2.2.2.2.2.2.2.2.2.2.2]; rfl
  have hx0 : (sf.regs.regs 0#5).truncate 8 = (r 0#5).truncate 8 := by
    rw [← hv]
    simp [State.readReg32, State.readReg64, RegFile.read]
  obtain ⟨sf', hs', hq⟩ := hcont sf hrunf hpc' hsp' hkept hvr hCLf (by rw [sepConj_comm]; exact hpost) hx0
  exact ⟨sf', Steps.trans' hst6 hs', hq⟩

end X25519Dalek.ESel
end

section
/-! # The remaining instruction shapes of block 6, on abstract states

One `ex_*` lemma (the instruction's effect on `mkS`) and one `r_*` lemma (a step of `Reach`) per
shape, in the style of `Steps.lean`/`Ssa.lean`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.ESel

open Arm64 Arm64.Obj

/-! ## Memory: 32-bit accesses -/

theorem memOK_write32 {m0 m : Memory} {W : BitVec 64 → Prop} (hW : WOwned m0 W)
    (h : MemOK m0 W m) {b : BitVec 64} (hb : AllB W b 4) (v : BitVec 32) :
    MemOK m0 W (m.write32 b v) := by
  have e : ∀ k : Nat, k < 4 → W (b + BitVec.ofNat 64 k) := hb
  unfold Memory.write32
  refine memOK_write8 hW (memOK_write8 hW (memOK_write8 hW (memOK_write8 hW h ?_ _) ?_ _) ?_ _) ?_ _
  · exact e 0 (by omega)
  · exact e 1 (by omega)
  · exact e 2 (by omega)
  · exact e 3 (by omega)

theorem allB_mono {W : BitVec 64 → Prop} {a : BitVec 64} {n k : Nat} (h : AllB W a n) (hk : k ≤ n) :
    AllB W a k := fun j hj => h j (by omega)

/-! ## Arithmetic and logic -/

section exec
variable {svc : State → State} {s : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {m : Memory} {ps : PState}

theorem ex_add_gsp {d : BitVec 5} (hd : d ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .ADD (.gpr d) .sp imm false) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (sp + imm.zeroExtend 64)) sp m ps := by
  show execAddSubImm .W64 .ADD (.gpr d) .sp imm false (mkS s pc r sp m ps) = _
  simp only [execAddSubImm, State.readReg, rd_sp, Bool.false_eq_true, if_false,
    evalAddSub_add, State.writeReg, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

theorem ex_addi {d n : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .ADD (.gpr d) (.gpr n) imm false) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (r n + imm.zeroExtend 64)) sp m ps := by
  show execAddSubImm .W64 .ADD (.gpr d) (.gpr n) imm false (mkS s pc r sp m ps) = _
  simp only [execAddSubImm, State.readReg, rd_gpr' _ _ _ _ _ _ _ hn,
    Bool.false_eq_true, if_false, evalAddSub_add, State.writeReg, wr_gpr _ _ _ _ _ _ _ _ hd,
    mkS_advancePC]

theorem ex_subi {d n : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .SUB (.gpr d) (.gpr n) imm false) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (r n - imm.zeroExtend 64)) sp m ps := by
  show execAddSubImm .W64 .SUB (.gpr d) (.gpr n) imm false (mkS s pc r sp m ps) = _
  simp only [execAddSubImm, State.readReg, rd_gpr' _ _ _ _ _ _ _ hn,
    Bool.false_eq_true, if_false, evalAddSub_sub, State.writeReg, wr_gpr _ _ _ _ _ _ _ _ hd,
    mkS_advancePC]

theorem awc_sub_z (x y : BitVec 64) :
    (AddWithCarry64 x (~~~y) true).2.z = decide (x = y) := by
  rw [show (AddWithCarry64 x (~~~y) true).2.z = ((AddWithCarry64 x (~~~y) true).1 == 0#64) from rfl,
    awc_sub]
  by_cases h : x = y
  · simp [h]
  · have : x - y ≠ 0#64 := fun e => h (by have := congrArg (· + y) e; simpa using this)
    simp [h, this]

theorem ex_cmpi {n : BitVec 5} (hn : n ≠ 31#5) (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .SUBS .xzr (.gpr n) imm false) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) r sp m (AddWithCarry64 (r n) (~~~(imm.zeroExtend 64)) true).2 := by
  show execAddSubImm .W64 .SUBS .xzr (.gpr n) imm false (mkS s pc r sp m ps) = _
  simp only [execAddSubImm, State.readReg, rd_gpr' _ _ _ _ _ _ _ hn,
    Bool.false_eq_true, if_false, evalAddSub, State.writeReg, wr_xzr, mkS_setPState, mkS_advancePC]
  simp

theorem ex_and {d n k : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W64 .AND (.gpr d) (.gpr n) (.gpr k) .LSL 0) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (r n &&& r k)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg, rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk,
    evalLogical, shiftVal, shift64, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]
  simp

theorem ex_orr {d n k : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W64 .ORR (.gpr d) (.gpr n) (.gpr k) .LSL 0) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (r n ||| r k)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg, rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk,
    evalLogical, shiftVal, shift64, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]
  simp

theorem ex_eor {d n k : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W64 .EOR (.gpr d) (.gpr n) (.gpr k) .LSL 0) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (r n ^^^ r k)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg, rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk,
    evalLogical, shiftVal, shift64, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]
  simp

theorem ex_movzz {d : BitVec 5} (hd : d ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W64 .ORR (.gpr d) .xzr .xzr .LSL 0) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d 0#64) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg, rd_xzr, evalLogical, shiftVal, shift64,
    wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]
  simp

theorem ex_orri_z {d : BitVec 5} (hd : d ≠ 31#5) (imm : BitVec 64) :
    execInstWithSvc svc (.logicalImm .W64 .ORR (.gpr d) .xzr imm) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d imm) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg, rd_xzr, evalLogical, wr_gpr _ _ _ _ _ _ _ _ hd,
    mkS_advancePC]
  simp

theorem ex_neg {d k : BitVec 5} (hd : d ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .SUB (.gpr d) .xzr (.gpr k) .LSL 0) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (0#64 - r k)) sp m ps := by
  show execAddSubShift .W64 .SUB (.gpr d) .xzr (.gpr k) .LSL 0 (mkS s pc r sp m ps) = _
  simp only [execAddSubShift, State.writeReg, State.readReg, rd_xzr,
    rd_gpr' _ _ _ _ _ _ _ hk, shiftVal, shift64, evalAddSub_sub, wr_gpr _ _ _ _ _ _ _ _ hd,
    mkS_advancePC]
  simp

theorem ex_sub {d n k : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .SUB (.gpr d) (.gpr n) (.gpr k) .LSL 0) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (r n - r k)) sp m ps := by
  show execAddSubShift .W64 .SUB (.gpr d) (.gpr n) (.gpr k) .LSL 0 (mkS s pc r sp m ps) = _
  simp only [execAddSubShift, State.writeReg, State.readReg,
    rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk, shiftVal, shift64, evalAddSub_sub,
    wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]
  simp

theorem ex_add32 {d n k : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W32 .ADD (.gpr d) (.gpr n) (.gpr k) .LSL 0) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d
        (((r n).truncate 32 + (r k).truncate 32).zeroExtend 64)) sp m ps := by
  show execAddSubShift .W32 .ADD (.gpr d) (.gpr n) (.gpr k) .LSL 0 (mkS s pc r sp m ps) = _
  simp only [execAddSubShift, State.writeReg, State.readReg, State.readReg32,
    rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk, shiftVal, shift32, evalAddSub,
    wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]
  simp only [Bool.false_eq_true, if_false, mkS_advancePC, Nat.zero_mod, BitVec.shiftLeft_zero]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry32, BitVec.toNat_setWidth] <;> omega

theorem ex_eor32 {d n k : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W32 .EOR (.gpr d) (.gpr n) (.gpr k) .LSL 0) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d
        (((r n).truncate 32 ^^^ (r k).truncate 32).zeroExtend 64)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W32 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg, State.readReg32, rd_gpr' _ _ _ _ _ _ _ hn,
    rd_gpr' _ _ _ _ _ _ _ hk, evalLogical, shiftVal, shift32, wr_gpr _ _ _ _ _ _ _ _ hd,
    mkS_advancePC]
  congr 2
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi] <;> omega

theorem ex_andi32 {d n : BitVec 5} {mask : BitVec 64} (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.logicalImm .W32 .AND (.gpr d) (.gpr n) mask) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d
        (((r n).truncate 32 &&& mask.truncate 32).zeroExtend 64)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W32 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg, State.readReg32, rd_gpr' _ _ _ _ _ _ _ hn,
    evalLogical, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]
  congr 2
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi] <;> omega

theorem ex_cmp_uxth {n k : BitVec 5} (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubExt .W32 .SUBS .xzr (.gpr n) (.gpr k) .UXTH 0) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) r sp m
        (AddWithCarry32 ((r n).truncate 32) (~~~(((r k).truncate 16).zeroExtend 32)) true).2 := by
  show execAddSubExt .W32 .SUBS .xzr (.gpr n) (.gpr k) .UXTH 0 (mkS s pc r sp m ps) = _
  simp only [execAddSubExt, State.writeReg, State.readReg, State.readReg32,
    rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk, extendVal, evalAddSub, wr_xzr,
    mkS_setPState, mkS_advancePC, if_true]
  congr 3
  · apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
  · apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi] <;> omega

theorem ex_cset_eq {d : BitVec 5} (hd : d ≠ 31#5) :
    execInstWithSvc svc (.condSelect .W32 .CSINC (.gpr d) .xzr .xzr .NE) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (if ps.z then 1#64 else 0#64)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W32 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg, State.readReg32, rd_xzr, ConditionHolds, mkS_pstate,
    wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]
  by_cases h : ps.z <;> simp [h]

theorem ex_bfm32 {d n : BitVec 5} {op : BitfieldOp} {immr imms : Nat} (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.bitfield .W32 op (.gpr d) (.gpr n) immr imms) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (((evalBitfield .W32 op (((r d).truncate 32).zeroExtend 64)
        (((r n).truncate 32).zeroExtend 64) immr imms).truncate 32).zeroExtend 64)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W32 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg, State.readReg32, rd_gpr' _ _ _ _ _ _ _ hn,
    rd_gpr' _ _ _ _ _ _ _ hd, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

theorem ex_bfm64 {d n : BitVec 5} {op : BitfieldOp} {immr imms : Nat} (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.bitfield .W64 op (.gpr d) (.gpr n) immr imms) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (evalBitfield .W64 op (r d) (r n) immr imms)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg, rd_gpr' _ _ _ _ _ _ _ hn,
    rd_gpr' _ _ _ _ _ _ _ hd, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

theorem ex_movn {d : BitVec 5} {imm : BitVec 16} (hd : d ≠ 31#5) :
    execInstWithSvc svc (.moveWide .W64 .MOVN (.gpr d) imm 0) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (~~~(imm.zeroExtend 64))) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]
  simp

theorem ex_movk48 {d : BitVec 5} {imm : BitVec 16} (hd : d ≠ 31#5) :
    execInstWithSvc svc (.moveWide .W64 .MOVK (.gpr d) imm 48) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d
        ((r d &&& ~~~(0xffff#64 <<< 48)) ||| (imm.zeroExtend 64 <<< 48))) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg, rd_gpr' _ _ _ _ _ _ _ hd, wr_gpr _ _ _ _ _ _ _ _ hd,
    mkS_advancePC]

theorem ex_umaddl {d n k a : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (ha : a ≠ 31#5) :
    execInstWithSvc svc (.dataProc3 .W64 .UMADDL (.gpr d) (.gpr n) (.gpr k) (.gpr a)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d
        (r a + ((r n).truncate 32).zeroExtend 64 * ((r k).truncate 32).zeroExtend 64)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg32, rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk,
    rd_gpr' _ _ _ _ _ _ _ ha, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

/-! ## Memory accesses -/

theorem ex_ldur {d : BitVec 5} {B : Reg} {bv off : BitVec 64} (hd : d ≠ 31#5)
    (hB : (mkS s pc r sp m ps).readReg64 B = bv) (hal : checkRegSPAligned (mkS s pc r sp m ps) B = true)
    (hrd : m.canRead (bv + off) 8 = true) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr d) (.UnscaledOffset B off)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (m.read64 (bv + off))) sp m ps := by
  show execLdr .W64 .X64 false (.gpr d) (.UnscaledOffset B off) (mkS s pc r sp m ps) = _
  simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, hB, mkS_mem, MemWidth.bytes, hrd,
    Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

theorem ex_stur {t : BitVec 5} {B : Reg} {bv off : BitVec 64} (ht : t ≠ 31#5)
    (hB : (mkS s pc r sp m ps).readReg64 B = bv) (hal : checkRegSPAligned (mkS s pc r sp m ps) B = true)
    (hw : m.canWrite (bv + off) 8 = true) :
    execInstWithSvc svc (.str .X64 (.gpr t) (.UnscaledOffset B off)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) r sp (m.write64 (bv + off) (r t)) ps := by
  show execStr .X64 (.gpr t) (.UnscaledOffset B off) (mkS s pc r sp m ps) = _
  simp only [execStr, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, hB, mkS_mem, MemWidth.bytes, hw,
    rd_gpr' _ _ _ _ _ _ _ ht, Memory.writeSized, mkS_setMem, mkS_advancePC]

theorem ex_strz {B : Reg} {bv off : BitVec 64}
    (hB : (mkS s pc r sp m ps).readReg64 B = bv) (hal : checkRegSPAligned (mkS s pc r sp m ps) B = true)
    (hw : m.canWrite (bv + off) 8 = true) :
    execInstWithSvc svc (.str .X64 .xzr (.Offset B off)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) r sp (m.write64 (bv + off) 0#64) ps := by
  show execStr .X64 .xzr (.Offset B off) (mkS s pc r sp m ps) = _
  simp only [execStr, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, hB, mkS_mem, MemWidth.bytes, hw,
    rd_xzr, Memory.writeSized, mkS_setMem, mkS_advancePC]

theorem ex_stpzz {B : Reg} {bv off : BitVec 64}
    (hB : (mkS s pc r sp m ps).readReg64 B = bv) (hal : checkRegSPAligned (mkS s pc r sp m ps) B = true)
    (hw1 : m.canWrite (bv + off) 8 = true) (hw2 : m.canWrite (bv + off + 8#64) 8 = true) :
    execInstWithSvc svc (.stp .W64 .xzr .xzr (.Offset B off)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) r sp ((m.write64 (bv + off) 0#64).write64 (bv + off + 8#64) 0#64) ps := by
  show execStp .W64 .xzr .xzr (.Offset B off) (mkS s pc r sp m ps) = _
  simp only [execStp, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, hB, mkS_mem, MemWidth.bytes, hw1, hw2,
    Bool.and_self, rd_xzr, Memory.writeSized, mkS_setMem, mkS_advancePC]

theorem ex_str32 {t : BitVec 5} {B : Reg} {bv off : BitVec 64} (ht : t ≠ 31#5)
    (hB : (mkS s pc r sp m ps).readReg64 B = bv) (hal : checkRegSPAligned (mkS s pc r sp m ps) B = true)
    (hw : m.canWrite (bv + off) 4 = true) :
    execInstWithSvc svc (.str .W32 (.gpr t) (.Offset B off)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) r sp (m.write32 (bv + off) ((r t).truncate 32)) ps := by
  show execStr .W32 (.gpr t) (.Offset B off) (mkS s pc r sp m ps) = _
  simp only [execStr, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, hB, mkS_mem, MemWidth.bytes, hw,
    rd_gpr' _ _ _ _ _ _ _ ht, Memory.writeSized, mkS_setMem, mkS_advancePC]

theorem ex_stp32 {t1 t2 : BitVec 5} {B : Reg} {bv off : BitVec 64} (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5)
    (hB : (mkS s pc r sp m ps).readReg64 B = bv) (hal : checkRegSPAligned (mkS s pc r sp m ps) B = true)
    (hw1 : m.canWrite (bv + off) 4 = true) (hw2 : m.canWrite (bv + off + 4#64) 4 = true) :
    execInstWithSvc svc (.stp .W32 (.gpr t1) (.gpr t2) (.Offset B off)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) r sp ((m.write32 (bv + off) ((r t1).truncate 32)).write32 (bv + off + 4#64)
        ((r t2).truncate 32)) ps := by
  show execStp .W32 (.gpr t1) (.gpr t2) (.Offset B off) (mkS s pc r sp m ps) = _
  simp only [execStp, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, hB, mkS_mem, MemWidth.bytes, hw1, hw2,
    Bool.and_self, rd_gpr' _ _ _ _ _ _ _ ht1, rd_gpr' _ _ _ _ _ _ _ ht2, Memory.writeSized,
    mkS_setMem, mkS_advancePC]

theorem ex_ldp32 {d1 d2 : BitVec 5} {B : Reg} {bv off : BitVec 64} (hd1 : d1 ≠ 31#5) (hd2 : d2 ≠ 31#5)
    (hB : (mkS s pc r sp m ps).readReg64 B = bv) (hal : checkRegSPAligned (mkS s pc r sp m ps) B = true)
    (hrd1 : m.canRead (bv + off) 4 = true) (hrd2 : m.canRead (bv + off + 4#64) 4 = true) :
    execInstWithSvc svc (.ldp .W32 false (.gpr d1) (.gpr d2) (.Offset B off)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update (Function.update r d1 ((m.read32 (bv + off)).zeroExtend 64)) d2
        ((m.read32 (bv + off + 4#64)).zeroExtend 64)) sp m ps := by
  show execLdp .W32 false (.gpr d1) (.gpr d2) (.Offset B off) (mkS s pc r sp m ps) = _
  simp only [execLdp, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, hB, mkS_mem, MemWidth.bytes, hrd1, hrd2,
    Bool.and_self, Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ _ hd1,
    wr_gpr _ _ _ _ _ _ _ _ hd2, mkS_advancePC]
  congr 3
  · apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi] <;> omega
  · apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi] <;> omega

theorem ex_ldr32 {d : BitVec 5} {B : Reg} {bv off : BitVec 64} (hd : d ≠ 31#5)
    (hB : (mkS s pc r sp m ps).readReg64 B = bv) (hal : checkRegSPAligned (mkS s pc r sp m ps) B = true)
    (hrd : m.canRead (bv + off) 4 = true) :
    execInstWithSvc svc (.ldr .W32 .W32 false (.gpr d) (.Offset B off)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d ((m.read32 (bv + off)).zeroExtend 64)) sp m ps := by
  show execLdr .W32 .W32 false (.gpr d) (.Offset B off) (mkS s pc r sp m ps) = _
  simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, hB, mkS_mem, MemWidth.bytes, hrd,
    Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]
  congr 2
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi] <;> omega

end exec


/-! ## Steps of `Reach` -/

section ssa
variable {mpl : MultiPlacement} {i : Nat} {P : State → Prop} {s : State} {pcb : BitVec 64}
  {n : Nat} {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {m m0 : Memory} {ps : PState}
  {W : BitVec 64 → Prop}

theorem r_add_gsp {d : BitVec 5} {imm : BitVec 12} (hd : d ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.addSubImm .W64 .ADD (.gpr d) .sp imm false))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d (sp + imm.zeroExtend 64)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_add_gsp hd, pc_add4]; exact h)

theorem r_addi {d a : BitVec 5} {imm : BitVec 12} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.addSubImm .W64 .ADD (.gpr d) (.gpr a) imm false))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d (r a + imm.zeroExtend 64)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_addi hd ha, pc_add4]; exact h)

theorem r_subi {d a : BitVec 5} {imm : BitVec 12} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.addSubImm .W64 .SUB (.gpr d) (.gpr a) imm false))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d (r a - imm.zeroExtend 64)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_subi hd ha, pc_add4]; exact h)

theorem r_cmpi {a : BitVec 5} {imm : BitVec 12} (ha : a ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.addSubImm .W64 .SUBS .xzr (.gpr a) imm false))
    (h : ∀ ps' : PState, ps'.z = decide (r a = imm.zeroExtend 64) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r sp m ps')) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_cmpi ha, pc_add4]; exact h _ (awc_sub_z _ _))

theorem r_and {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.logicalShift .W64 .AND (.gpr d) (.gpr a) (.gpr b) .LSL 0))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d (r a &&& r b)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_and hd ha hb, pc_add4]; exact h)

theorem r_orr {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.logicalShift .W64 .ORR (.gpr d) (.gpr a) (.gpr b) .LSL 0))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d (r a ||| r b)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_orr hd ha hb, pc_add4]; exact h)

theorem r_eor {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.logicalShift .W64 .EOR (.gpr d) (.gpr a) (.gpr b) .LSL 0))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d (r a ^^^ r b)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_eor hd ha hb, pc_add4]; exact h)

theorem r_movzz {d : BitVec 5} (hd : d ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.logicalShift .W64 .ORR (.gpr d) .xzr .xzr .LSL 0))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d 0#64) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_movzz hd, pc_add4]; exact h)

theorem r_orri_z {d : BitVec 5} {imm : BitVec 64} (hd : d ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.logicalImm .W64 .ORR (.gpr d) .xzr imm))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d imm) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_orri_z hd, pc_add4]; exact h)

theorem r_neg {d b : BitVec 5} (hd : d ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.addSubShift .W64 .SUB (.gpr d) .xzr (.gpr b) .LSL 0))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d (0#64 - r b)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_neg hd hb, pc_add4]; exact h)

theorem r_sub {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.addSubShift .W64 .SUB (.gpr d) (.gpr a) (.gpr b) .LSL 0))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d (r a - r b)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_sub hd ha hb, pc_add4]; exact h)

theorem r_add32 {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.addSubShift .W32 .ADD (.gpr d) (.gpr a) (.gpr b) .LSL 0))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r d (((r a).truncate 32 + (r b).truncate 32).zeroExtend 64)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_add32 hd ha hb, pc_add4]; exact h)

theorem r_eor32 {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.logicalShift .W32 .EOR (.gpr d) (.gpr a) (.gpr b) .LSL 0))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r d (((r a).truncate 32 ^^^ (r b).truncate 32).zeroExtend 64)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_eor32 hd ha hb, pc_add4]; exact h)

theorem r_andi32 {d a : BitVec 5} {mask : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.logicalImm .W32 .AND (.gpr d) (.gpr a) mask))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r d (((r a).truncate 32 &&& mask.truncate 32).zeroExtend 64)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_andi32 hd ha, pc_add4]; exact h)

theorem r_cmp_uxth {a b : BitVec 5} (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.addSubExt .W32 .SUBS .xzr (.gpr a) (.gpr b) .UXTH 0))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r sp m
      (AddWithCarry32 ((r a).truncate 32) (~~~(((r b).truncate 16).zeroExtend 32)) true).2)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_cmp_uxth ha hb, pc_add4]; exact h)

theorem r_cset_eq {d : BitVec 5} (hd : d ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.condSelect .W32 .CSINC (.gpr d) .xzr .xzr .NE))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r d (if ps.z then 1#64 else 0#64)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_cset_eq hd, pc_add4]; exact h)

theorem r_bfm32 {d a : BitVec 5} {op : BitfieldOp} {immr imms : Nat} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.bitfield .W32 op (.gpr d) (.gpr a) immr imms))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r d (((evalBitfield .W32 op (((r d).truncate 32).zeroExtend 64)
        (((r a).truncate 32).zeroExtend 64) immr imms).truncate 32).zeroExtend 64)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_bfm32 hd ha, pc_add4]; exact h)

theorem r_bfm64 {d a : BitVec 5} {op : BitfieldOp} {immr imms : Nat} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.bitfield .W64 op (.gpr d) (.gpr a) immr imms))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r d (evalBitfield .W64 op (r d) (r a) immr imms)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_bfm64 hd ha, pc_add4]; exact h)

theorem r_movn {d : BitVec 5} {imm : BitVec 16} (hd : d ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.moveWide .W64 .MOVN (.gpr d) imm 0))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d (~~~(imm.zeroExtend 64))) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_movn hd, pc_add4]; exact h)

theorem r_movk48 {d : BitVec 5} {imm : BitVec 16} (hd : d ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.moveWide .W64 .MOVK (.gpr d) imm 48))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r d ((r d &&& ~~~(0xffff#64 <<< 48)) ||| (imm.zeroExtend 64 <<< 48))) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_movk48 hd, pc_add4]; exact h)

theorem r_umaddl {d a b c : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hc : c ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.dataProc3 .W64 .UMADDL (.gpr d) (.gpr a) (.gpr b) (.gpr c)))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d
      (r c + ((r a).truncate 32).zeroExtend 64 * ((r b).truncate 32).zeroExtend 64)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_umaddl hd ha hb hc, pc_add4]; exact h)

theorem r_ldur_g {d b : BitVec 5} {off : BitVec 64} (hd : d ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.ldr .W64 .X64 false (.gpr d) (.UnscaledOffset (.gpr b) off)))
    (hrd : m.canRead (r b + off) 8 = true)
    (h : ∀ t, t = m.read64 (r b + off) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by
    rw [ex_ldur hd (rd_gpr' _ _ _ _ _ _ _ hb) (checkGpr ..) hrd, pc_add4]; exact h _ rfl)

theorem r_stur_g {t b : BitVec 5} {off : BitVec 64} (ht : t ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.str .X64 (.gpr t) (.UnscaledOffset (.gpr b) off)))
    (hw : AllB W (r b + off) 8)
    (h : MemOK m0 W (m.write64 (r b + off) (r t)) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r sp (m.write64 (r b + off) (r t)) ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by
    rw [ex_stur ht (rd_gpr' _ _ _ _ _ _ _ hb) (checkGpr ..) (canWrite_of hW hok hw), pc_add4]
    exact h (memOK_write64 hW hok hw _))

theorem r_strz_sp {off : BitVec 64} (hsp : sp.toNat % 16 = 0)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.str .X64 .xzr (.Offset .sp off)))
    (hw : AllB W (sp + off) 8)
    (h : MemOK m0 W (m.write64 (sp + off) 0#64) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r sp (m.write64 (sp + off) 0#64) ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by
    rw [ex_strz (rd_sp ..) (checkSP _ _ _ _ _ _ hsp) (canWrite_of hW hok hw), pc_add4]
    exact h (memOK_write64 hW hok hw _))

theorem r_stpzz_sp {off : BitVec 64} (hsp : sp.toNat % 16 = 0)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.stp .W64 .xzr .xzr (.Offset .sp off)))
    (hw1 : AllB W (sp + off) 8) (hw2 : AllB W (sp + off + 8#64) 8)
    (h : MemOK m0 W ((m.write64 (sp + off) 0#64).write64 (sp + off + 8#64) 0#64) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r sp
        ((m.write64 (sp + off) 0#64).write64 (sp + off + 8#64) 0#64) ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  have hok1 := memOK_write64 hW hok hw1 0#64
  exact reach_mk hrun hW hok hf (by
    rw [ex_stpzz (rd_sp ..) (checkSP _ _ _ _ _ _ hsp) (canWrite_of hW hok hw1)
      (canWrite_of hW hok hw2), pc_add4]
    exact h (memOK_write64 hW hok1 hw2 _))

theorem r_stpzz_g {b : BitVec 5} {off : BitVec 64} (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.stp .W64 .xzr .xzr (.Offset (.gpr b) off)))
    (hw1 : AllB W (r b + off) 8) (hw2 : AllB W (r b + off + 8#64) 8)
    (h : MemOK m0 W ((m.write64 (r b + off) 0#64).write64 (r b + off + 8#64) 0#64) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r sp
        ((m.write64 (r b + off) 0#64).write64 (r b + off + 8#64) 0#64) ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  have hok1 := memOK_write64 hW hok hw1 0#64
  exact reach_mk hrun hW hok hf (by
    rw [ex_stpzz (rd_gpr' _ _ _ _ _ _ _ hb) (checkGpr ..) (canWrite_of hW hok hw1)
      (canWrite_of hW hok hw2), pc_add4]
    exact h (memOK_write64 hW hok1 hw2 _))

theorem r_str32_sp {t : BitVec 5} {off : BitVec 64} (ht : t ≠ 31#5) (hsp : sp.toNat % 16 = 0)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.str .W32 (.gpr t) (.Offset .sp off)))
    (hw : AllB W (sp + off) 4)
    (h : MemOK m0 W (m.write32 (sp + off) ((r t).truncate 32)) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r sp (m.write32 (sp + off) ((r t).truncate 32)) ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by
    rw [ex_str32 ht (rd_sp ..) (checkSP _ _ _ _ _ _ hsp) (canWrite_of hW hok hw), pc_add4]
    exact h (memOK_write32 hW hok hw _))

theorem r_stp32_sp {t1 t2 : BitVec 5} {off : BitVec 64} (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5)
    (hsp : sp.toNat % 16 = 0)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.stp .W32 (.gpr t1) (.gpr t2) (.Offset .sp off)))
    (hw1 : AllB W (sp + off) 4) (hw2 : AllB W (sp + off + 4#64) 4)
    (h : MemOK m0 W ((m.write32 (sp + off) ((r t1).truncate 32)).write32 (sp + off + 4#64) ((r t2).truncate 32)) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r sp
        ((m.write32 (sp + off) ((r t1).truncate 32)).write32 (sp + off + 4#64) ((r t2).truncate 32)) ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  have hok1 := memOK_write32 hW hok hw1 ((r t1).truncate 32)
  exact reach_mk hrun hW hok hf (by
    rw [ex_stp32 ht1 ht2 (rd_sp ..) (checkSP _ _ _ _ _ _ hsp) (canWrite_of hW hok hw1)
      (canWrite_of hW hok hw2), pc_add4]
    exact h (memOK_write32 hW hok1 hw2 _))

theorem r_ldp32_sp {d1 d2 : BitVec 5} {off : BitVec 64} (hd1 : d1 ≠ 31#5) (hd2 : d2 ≠ 31#5)
    (hsp : sp.toNat % 16 = 0)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.ldp .W32 false (.gpr d1) (.gpr d2) (.Offset .sp off)))
    (hrd1 : m.canRead (sp + off) 4 = true) (hrd2 : m.canRead (sp + off + 4#64) 4 = true)
    (h : ∀ t1 t2, t1 = m.read32 (sp + off) → t2 = m.read32 (sp + off + 4#64) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
        (Function.update (Function.update r d1 (t1.zeroExtend 64)) d2 (t2.zeroExtend 64)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by
    rw [ex_ldp32 hd1 hd2 (rd_sp ..) (checkSP _ _ _ _ _ _ hsp) hrd1 hrd2, pc_add4]; exact h _ _ rfl rfl)

theorem r_ldr32_sp {d : BitVec 5} {off : BitVec 64} (hd : d ≠ 31#5) (hsp : sp.toNat % 16 = 0)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.ldr .W32 .W32 false (.gpr d) (.Offset .sp off)))
    (hrd : m.canRead (sp + off) 4 = true)
    (h : ∀ t, t = m.read32 (sp + off) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d (t.zeroExtend 64)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by
    rw [ex_ldr32 hd (rd_sp ..) (checkSP _ _ _ _ _ _ hsp) hrd, pc_add4]; exact h _ rfl)

theorem r_bne {off : BitVec 64} {c : Bool} (hz : ps.z = c)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.bCond .NE off))
    (h : Reach mpl i P (mkS s (if c then pcb + BitVec.ofNat 64 (n + 4) else pcb + BitVec.ofNat 64 n + off)
      r sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  refine reach_mk hrun hW hok hf ?_
  show Reach mpl i P (if ConditionHolds .NE ps then _ else _)
  simp only [ConditionHolds, hz]
  cases c
  · simpa using h
  · simpa [pc_add4] using h

end ssa

end X25519Dalek.ESel
end

section
/-! # Block 6: instruction fetch (generated by tools/gen_fetch.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.ESel

open Arm64 Arm64.Obj

theorem blk06_len : x25519CliBlk06.code.length = 764 := by decide +kernel

section fetch
variable {mpl : MultiPlacement} {m : Memory} (hCL : (prog mpl 6).CodeLoaded m)
include hCL

theorem f06 {off : Nat} {inst : Instr} (hal : off % 4 = 0) (hlen : off + 4 ≤ 764)
    (hr : x25519CliBlk06.relocAt? off = none) (hd : decode (x25519CliBlk06.wordAt off) = some inst) :
    rawFetch m (mpl.base 6 + BitVec.ofNat 64 off) = some inst :=
  fetch_plain blk06 (by rw [blk06_len]) hCL hal (by rw [blk06_len]; exact hlen) hr hd

theorem f06_0 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 0) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.sp) (Arm64.Reg.sp) 0x0b0#12 false) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_4 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 4) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000050#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_8 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 8) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x1b#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000060#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_12 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 12) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x19#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000070#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_16 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 16) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x17#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000080#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_20 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 20) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000090#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_24 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 24) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000a0#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_28 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 28) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.sp) 0x050#12 false) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_32 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 32) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.SBFM) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x02#5) 0 7) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_36 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 36) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.SBFM) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x02#5) 7 7) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_40 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 40) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_44 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 44) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x1b#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_48 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 48) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_52 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 52) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_56 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 56) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_60 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 60) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_64 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 64) =
    some (Arm64.Instr.str (Arm64.MemWidth.W32) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000004#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_68 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 68) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_72 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 72) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.gpr 0x01#5) 0x038#12 false) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_76 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 76) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x1a#5) 0x0001#16 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_80 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 80) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x15#5) 0x0001#16 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_84 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 84) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x17#5) 0x0001#16 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_88 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 88) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000008#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_92 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 92) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000018#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_96 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 96) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffe0#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_100 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 100) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.xzr) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000028#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_104 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 104) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x1d#5) 0xfffffffffffffff0#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_108 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 108) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W32) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_112 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 112) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_116 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 116) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W32) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x1a#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_120 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 120) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) 0x0000ffff0000ffff#64) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_124 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 124) =
    some (Arm64.Instr.addSubExt (Arm64.RegWidth.W32) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ExtendType.UXTH) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_128 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 128) =
    some (Arm64.Instr.condSelect (Arm64.RegWidth.W32) (Arm64.CondSelectOp.CSINC) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.CondCode.NE)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_136 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 136) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x19#5) 0xffffffffffffffc8#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_140 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 140) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x00#5) 0x00000000000000ff#64) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_144 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 144) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000018#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_148 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 148) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_152 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 152) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) 0x001#12 false) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_156 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 156) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x1a#5) 0x001#12 false) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_160 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 160) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x15#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_164 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 164) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_168 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 168) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_172 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 172) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x15#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_176 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 176) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x19#5) 0xffffffffffffffd8#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_180 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 180) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_184 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 184) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_188 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 188) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x1a#5) 0x009#12 false) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_192 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 192) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_196 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 196) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000020#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_200 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 200) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffe8#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_204 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 204) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_208 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 208) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_212 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 212) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_216 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 216) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_220 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 220) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000018#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_224 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 224) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_228 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 228) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffe0#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_232 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 232) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffe8#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_236 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 236) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x19#5) 0xffffffffffffffe8#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_240 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 240) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_244 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 244) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_248 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 248) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x19#5) 0xfffffffffffffff8#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_252 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 252) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_256 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 256) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_260 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 260) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_264 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 264) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffe0#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_268 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 268) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x17#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_272 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 272) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x17#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_276 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 276) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000028#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_280 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 280) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_284 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 284) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_288 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 288) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_292 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 292) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_296 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 296) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x19#5) 0x0000000000000008#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_300 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 300) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_304 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 304) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000028#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_308 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 308) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x1d#5) 0xfffffffffffffff0#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_312 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 312) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_316 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 316) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_320 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 320) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_324 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 324) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_328 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 328) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_332 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 332) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_336 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 336) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x1d#5) 0xfffffffffffffff0#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_340 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 340) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_344 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 344) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x1d#5) 0xfffffffffffffff8#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_348 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 348) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x19#5) 0x0000000000000018#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_352 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 352) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_356 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 356) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x19#5) 0x0000000000000028#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_360 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 360) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_364 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 364) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_368 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 368) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_372 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 372) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_376 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 376) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x19#5) 0x0000000000000038#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_380 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 380) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_384 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 384) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_388 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 388) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_392 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 392) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x1b#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_396 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 396) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_400 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 400) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_404 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 404) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_408 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 408) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_412 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 412) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x1b#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_416 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 416) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.gpr 0x19#5) 0x078#12 false) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_420 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 420) =
    some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0xfffffffffffffecc#64) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_424 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 424) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.W32) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000004#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_428 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 428) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x08#5) 7 7) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_436 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 436) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVN) (Arm64.Reg.gpr 0x08#5) 0x012f#16 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_440 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 440) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr) 0x007ffffffffffff0#64) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_444 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 444) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x11#5) 0x0013#16 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_448 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 448) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVK) (Arm64.Reg.gpr 0x08#5) 0x007f#16 48) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_452 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 452) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x1b#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_456 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 456) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x14#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_460 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 460) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x18#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_464 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 464) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W64) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0c#5) 51 63) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_468 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 468) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x13#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_472 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 472) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x1c#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_476 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 476) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x08#5) 0x0007ffffffffffff#64) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_480 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 480) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0a#5) 0x0007ffffffffffff#64) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_484 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 484) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x0c#5) 0x0007ffffffffffff#64) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_488 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 488) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMADDL) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x0e#5)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_492 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 492) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSR) 51) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_496 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 496) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x00#5) 0x00000000000000ff#64) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_500 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 500) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSR) 51) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_504 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 504) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x09#5) 0x0007ffffffffffff#64) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_508 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 508) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000018#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_512 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 512) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_516 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 516) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x15#5) (Arm64.Reg.gpr 0x17#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_520 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 520) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0b#5) 0x0007ffffffffffff#64) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_524 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 524) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x17#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_528 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 528) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_532 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 532) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x17#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffe8#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_536 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 536) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.ShiftType.LSR) 51) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_540 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 540) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSR) 51) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_544 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 544) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x16#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_548 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 548) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x16#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_552 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 552) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x16#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000028#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_556 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 556) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x15#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_560 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 560) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x1d#5) 0xfffffffffffffff8#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_564 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 564) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x07#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x1d#5) 0xffffffffffffffe0#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_568 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 568) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_572 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 572) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000008#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_576 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 576) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x16#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_580 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 580) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_584 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 584) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x17#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_588 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 588) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x15#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_592 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 592) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_596 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 596) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0x0000000000000000#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_600 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 600) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_604 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 604) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_608 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 608) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_612 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 612) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x07#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_616 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 616) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x19#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_620 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 620) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x05#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_624 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 624) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x16#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_628 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 628) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0e#5) 0x001#12 false) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_632 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 632) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0x0000000000000020#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_636 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 636) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_640 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 640) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_644 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 644) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x11#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0x0000000000000030#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_648 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 648) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_652 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 652) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_656 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 656) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x06#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_660 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 660) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_664 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 664) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x10#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_668 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 668) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_672 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 672) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_676 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 676) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_680 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 680) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_684 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 684) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_688 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 688) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x1b#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_692 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 692) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0x0000000000000010#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_696 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 696) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x17#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_700 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 700) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.EOR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x15#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_704 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 704) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_708 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 708) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x10#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_712 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 712) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_716 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 716) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0x0000000000000040#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_720 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 720) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0x0000000000000050#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_724 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 724) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0x0000000000000060#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_728 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 728) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0x0000000000000070#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_732 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 732) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000a0#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_736 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 736) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000090#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_740 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 740) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x17#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000080#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_744 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 744) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x19#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000070#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_748 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 748) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x1b#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000060#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_752 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 752) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000050#64)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_756 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 756) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.sp) (Arm64.Reg.sp) 0x0b0#12 false) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem f06_760 : rawFetch m (mpl.base 6 + BitVec.ofNat 64 760) =
    some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) :=
  f06 hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)

end fetch

end X25519Dalek.ESel
end

section
/-! # 32-bit reads and writes against 32/64-bit writes at disjoint addresses -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.ESel

open Arm64 Arm64.Obj

/-- The ranges `[a, a + na)` and `[b, b + nb)` are disjoint. -/
def FarN (a : BitVec 64) (na : Nat) (b : BitVec 64) (nb : Nat) : Prop :=
  na ≤ (b - a).toNat ∧ nb ≤ (a - b).toNat

theorem farN_add_iff (b c1 c2 : BitVec 64) (na nb : Nat) :
    FarN (b + c1) na (b + c2) nb ↔ na ≤ (c2 - c1).toNat ∧ nb ≤ (c1 - c2).toNat := by
  unfold FarN
  rw [show b + c2 - (b + c1) = c2 - c1 by bv_omega, show b + c1 - (b + c2) = c1 - c2 by bv_omega]

theorem ne_of_farN {a b : BitVec 64} {na nb : Nat} (h : FarN a na b nb) (i j : Nat) (hi : i < na)
    (hj : j < nb) : b + BitVec.ofNat 64 j ≠ a + BitVec.ofNat 64 i := by
  intro e
  obtain ⟨h1, h2⟩ := h
  have he := congrArg BitVec.toNat e
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at he
  rw [BitVec.toNat_sub] at h1 h2
  have ha := a.isLt
  have hb := b.isLt
  have hna : na ≤ 2 ^ 64 := by
    have := (b - a).isLt; rw [BitVec.toNat_sub] at this; omega
  have hnb : nb ≤ 2 ^ 64 := by
    have := (a - b).isLt; rw [BitVec.toNat_sub] at this; omega
  rw [Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)] at he
  omega

theorem read32_write8_ne (m : Memory) (a b : BitVec 64) (v : BitVec 8)
    (h : ∀ k : Nat, k < 4 → b + BitVec.ofNat 64 k ≠ a) : (m.write8 a v).read32 b = m.read32 b := by
  have h0 := h 0 (by omega)
  simp only [BitVec.add_zero] at h0
  simp only [Memory.read32, read8_write8, BitVec.add_zero, if_neg h0, if_neg (h 1 (by omega)),
    if_neg (h 2 (by omega)), if_neg (h 3 (by omega))]

theorem read64_write32_far (m : Memory) (a b : BitVec 64) (v : BitVec 32) (h : FarN a 4 b 8) :
    (m.write32 a v).read64 b = m.read64 b := by
  unfold Memory.write32
  have n := ne_of_farN h
  simp only []
  rw [read64_write8_ne, read64_write8_ne, read64_write8_ne, read64_write8_ne]
  all_goals intro k hk
  all_goals first
    | exact n 0 k (by omega) hk | exact n 1 k (by omega) hk | exact n 2 k (by omega) hk
    | exact n 3 k (by omega) hk | exact n 4 k (by omega) hk | exact n 5 k (by omega) hk
    | exact n 6 k (by omega) hk | exact n 7 k (by omega) hk | simpa using n 0 k (by omega) hk

theorem read32_write32_far (m : Memory) (a b : BitVec 64) (v : BitVec 32) (h : FarN a 4 b 4) :
    (m.write32 a v).read32 b = m.read32 b := by
  unfold Memory.write32
  have n := ne_of_farN h
  simp only []
  rw [read32_write8_ne, read32_write8_ne, read32_write8_ne, read32_write8_ne]
  all_goals intro k hk
  all_goals first
    | exact n 0 k (by omega) hk | exact n 1 k (by omega) hk | exact n 2 k (by omega) hk
    | exact n 3 k (by omega) hk | exact n 4 k (by omega) hk | exact n 5 k (by omega) hk
    | exact n 6 k (by omega) hk | exact n 7 k (by omega) hk | simpa using n 0 k (by omega) hk

theorem read32_write64_far (m : Memory) (a b : BitVec 64) (v : BitVec 64) (h : FarN a 8 b 4) :
    (m.write64 a v).read32 b = m.read32 b := by
  unfold Memory.write64
  have n := ne_of_farN h
  simp only []
  rw [read32_write8_ne, read32_write8_ne, read32_write8_ne, read32_write8_ne, read32_write8_ne,
    read32_write8_ne, read32_write8_ne, read32_write8_ne]
  all_goals intro k hk
  all_goals first
    | exact n 0 k (by omega) hk | exact n 1 k (by omega) hk | exact n 2 k (by omega) hk
    | exact n 3 k (by omega) hk | exact n 4 k (by omega) hk | exact n 5 k (by omega) hk
    | exact n 6 k (by omega) hk | exact n 7 k (by omega) hk | simpa using n 0 k (by omega) hk

theorem read8_write32_off (m : Memory) (a c : BitVec 64) (v : BitVec 32) (hc : c.toNat < 4) :
    (m.write32 a v).read8 (a + c) = v.extractLsb' (8 * c.toNat) 8 := by
  simp only [Memory.write32, read8_write8, bv_add_left_cancel]
  have : c = 0#64 ∨ c = 1#64 ∨ c = 2#64 ∨ c = 3#64 := by
    have : c.toNat = 0 ∨ c.toNat = 1 ∨ c.toNat = 2 ∨ c.toNat = 3 := by omega
    rcases this with e | e | e | e
    · left; exact BitVec.eq_of_toNat_eq (by simpa using e)
    · right; left; exact BitVec.eq_of_toNat_eq (by simpa using e)
    · right; right; left; exact BitVec.eq_of_toNat_eq (by simpa using e)
    · right; right; right; exact BitVec.eq_of_toNat_eq (by simpa using e)
  rcases this with rfl | rfl | rfl | rfl <;> simp

theorem read32_write32_same (m : Memory) (a : BitVec 64) (v : BitVec 32) :
    (m.write32 a v).read32 a = v := by
  have e := read8_write32_off m a
  unfold Memory.read32
  simp only []
  rw [e _ _ (by decide), e _ _ (by decide), e _ _ (by decide), e _ _ (by decide)]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

end X25519Dalek.ESel
end

section
/-! # Reading and writing one register of a literal register list (generated by tools/gen_regl.py)

One rewrite per access keeps the step proofs small (no `List.set`/`List.getD` unfolding). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.ESel

open Arm64

section
variable (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v : BitVec 64)

theorem regL_get_0 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 0#5 = x0 := rfl
theorem regL_get_1 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 1#5 = x1 := rfl
theorem regL_get_2 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 2#5 = x2 := rfl
theorem regL_get_3 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 3#5 = x3 := rfl
theorem regL_get_4 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 4#5 = x4 := rfl
theorem regL_get_5 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 5#5 = x5 := rfl
theorem regL_get_6 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 6#5 = x6 := rfl
theorem regL_get_7 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 7#5 = x7 := rfl
theorem regL_get_8 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 8#5 = x8 := rfl
theorem regL_get_9 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 9#5 = x9 := rfl
theorem regL_get_10 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 10#5 = x10 := rfl
theorem regL_get_11 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 11#5 = x11 := rfl
theorem regL_get_12 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 12#5 = x12 := rfl
theorem regL_get_13 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 13#5 = x13 := rfl
theorem regL_get_14 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 14#5 = x14 := rfl
theorem regL_get_15 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 15#5 = x15 := rfl
theorem regL_get_16 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 16#5 = x16 := rfl
theorem regL_get_17 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 17#5 = x17 := rfl
theorem regL_get_18 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 18#5 = x18 := rfl
theorem regL_get_19 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 19#5 = x19 := rfl
theorem regL_get_20 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 20#5 = x20 := rfl
theorem regL_get_21 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 21#5 = x21 := rfl
theorem regL_get_22 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 22#5 = x22 := rfl
theorem regL_get_23 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 23#5 = x23 := rfl
theorem regL_get_24 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 24#5 = x24 := rfl
theorem regL_get_25 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 25#5 = x25 := rfl
theorem regL_get_26 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 26#5 = x26 := rfl
theorem regL_get_27 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 27#5 = x27 := rfl
theorem regL_get_28 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 28#5 = x28 := rfl
theorem regL_get_29 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 29#5 = x29 := rfl
theorem regL_get_30 : regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] 30#5 = x30 := rfl

theorem regL_set_0 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 0#5 v = regL [v, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_1 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 1#5 v = regL [x0, v, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_2 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 2#5 v = regL [x0, x1, v, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_3 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 3#5 v = regL [x0, x1, x2, v, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_4 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 4#5 v = regL [x0, x1, x2, x3, v, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_5 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 5#5 v = regL [x0, x1, x2, x3, x4, v, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_6 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 6#5 v = regL [x0, x1, x2, x3, x4, x5, v, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_7 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 7#5 v = regL [x0, x1, x2, x3, x4, x5, x6, v, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_8 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 8#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, v, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_9 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 9#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, v, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_10 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 10#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, v, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_11 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 11#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, v, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_12 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 12#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, v, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_13 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 13#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, v, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_14 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 14#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, v, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_15 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 15#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, v, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_16 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 16#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, v, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_17 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 17#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, v, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_18 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 18#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, v, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_19 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 19#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, v, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_20 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 20#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, v, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_21 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 21#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, v, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_22 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 22#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, v, x23, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_23 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 23#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, v, x24, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_24 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 24#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, v, x25, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_25 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 25#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, v, x26, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_26 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 26#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, v, x27, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_27 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 27#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, v, x28, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_28 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 28#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, v, x29, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_29 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 29#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, v, x30, x31] :=
  regL_update _ _ _ rfl
theorem regL_set_30 : Function.update (regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31]) 30#5 v = regL [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, v, x31] :=
  regL_update _ _ _ rfl

end

theorem ne31_0 : (0#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_1 : (1#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_2 : (2#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_3 : (3#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_4 : (4#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_5 : (5#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_6 : (6#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_7 : (7#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_8 : (8#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_9 : (9#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_10 : (10#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_11 : (11#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_12 : (12#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_13 : (13#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_14 : (14#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_15 : (15#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_16 : (16#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_17 : (17#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_18 : (18#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_19 : (19#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_20 : (20#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_21 : (21#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_22 : (22#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_23 : (23#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_24 : (24#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_25 : (25#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_26 : (26#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_27 : (27#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_28 : (28#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_29 : (29#5 : BitVec 5) ≠ 31#5 := by decide
theorem ne31_30 : (30#5 : BitVec 5) ≠ 31#5 := by decide

end X25519Dalek.ESel
end

section
/-! # Meaning of the bitfield, mask and selection instructions of block 6 -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.ESel

open Arm64 Arm64.Obj

/-- `SXTB` of the low byte, as a 32-bit word. -/
def sxtbW (X : BitVec 64) : BitVec 32 := (X.truncate 8).signExtend 32

/-- The sign mask of the low byte, as a 32-bit word. -/
def signW (X : BitVec 64) : BitVec 32 := if X.getLsbD 7 then 0xffffffff#32 else 0#32

theorem tz32 (w : BitVec 32) : (w.zeroExtend 64).truncate 32 = w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem bf_sxtb (d X : BitVec 64) :
    ((evalBitfield .W32 .SBFM d ((X.truncate 32).zeroExtend 64) 0 7).truncate 32).zeroExtend 64 =
      (sxtbW X).zeroExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have k1 := (by decide : ∀ k (hk : k < 64), (255#64)[k] = decide (k < 8)) i hi
  have k2 := (by decide : ∀ k (hk : k < 64), (4294967040#64)[k] = decide (8 ≤ k ∧ k < 32)) i hi
  have k3 := (by decide : ∀ k (hk : k < 64), (18446744073709551615#64)[k] = true) i hi
  simp [evalBitfield, sxtbW, hi, k1, k2, BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last]
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 32) ∨ 32 ≤ i) with h | ⟨h1, h2⟩ | h
  · by_cases h7 : X[7] <;> simp [h7, k3, h, show i < 32 by omega]
  · by_cases h7 : X[7] <;> simp [h7, k3, h1, h2, show ¬ i < 8 by omega]
  · simp [show ¬ i < 32 by omega]

theorem bf_sign (d X : BitVec 64) :
    ((evalBitfield .W32 .SBFM d ((X.truncate 32).zeroExtend 64) 7 7).truncate 32).zeroExtend 64 =
      (signW X).zeroExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have k2 := (by decide : ∀ k (hk : k < 64), (4294967294#64)[k] = decide (1 ≤ k ∧ k < 32)) i hi
  simp [evalBitfield, signW, hi, k2]
  have k4 := (by decide : ∀ k (hk : k < 64), (4294967295#32).getLsbD k = decide (k < 32)) i hi
  have k3 := (by decide : ∀ k (hk : k < 64), (18446744073709551615#64)[k] = true) i hi
  rcases (by omega : i = 0 ∨ (1 ≤ i ∧ i < 32) ∨ 32 ≤ i) with h | ⟨h1, h2⟩ | h
  · subst h; by_cases h7 : X[7] <;> simp [h7]
  · by_cases h7 : X[7] <;> simp [h7, k3, k4, h1, h2, show i ≠ 0 by omega]
  · by_cases h7 : X[7] <;> simp [h7, k4, show ¬ i < 32 by omega]

theorem tz16 (w : BitVec 32) : (w.zeroExtend 64).truncate 16 = w.truncate 16 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi] <;> omega

theorem tr_ffff : BitVec.truncate 32 281470681808895#64 = 65535#32 := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.reduceSetWidth]

/-- The zero flag of `CMP W8, W9, UXTH` after `EOR W8, W8, W26; AND W8, W8, #0xffff`. -/
def CZ (w16 w20 : BitVec 32) (J : BitVec 64) : Bool :=
  (AddWithCarry32 ((w16 ^^^ J.truncate 32) &&& 65535#32) (~~~((w20.truncate 16).zeroExtend 32)) true).2.z

theorem neg_ite (c : Bool) :
    0#64 - (if c = true then 1#64 else 0#64) = if c = true then 18446744073709551615#64 else 0#64 := by
  cases c <;> rfl

theorem sub1_ite (c : Bool) :
    (if c = true then 1#64 else 0#64) - 1#64 = if c = true then 0#64 else 18446744073709551615#64 := by
  cases c <;> rfl

theorem ones64 : (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 := by decide

theorem and_m1 (x : BitVec 64) (c : Bool) :
    x &&& (if c = true then 18446744073709551615#64 else 0#64) = if c = true then x else 0#64 := by
  cases c
  · simp
  · simp only [if_true, ones64, BitVec.and_allOnes]

theorem and_m2 (x : BitVec 64) (c : Bool) :
    x &&& (if c = true then 0#64 else 18446744073709551615#64) = if c = true then 0#64 else x := by
  cases c
  · simp only [Bool.false_eq_true, if_false, ones64, BitVec.and_allOnes]
  · simp

theorem or_m (x y : BitVec 64) (c : Bool) :
    (if c = true then x else 0#64) ||| (if c = true then 0#64 else y) = if c = true then x else y := by
  cases c <;> simp

theorem bf_bit7 (d X : BitVec 64) :
    ((evalBitfield .W32 .UBFM d ((sxtbW X).zeroExtend 64) 7 7).truncate 32).zeroExtend 64 =
      if X.getLsbD 7 = true then 1#64 else 0#64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [evalBitfield, sxtbW, hi]
  rcases (by omega : i = 0 ∨ 1 ≤ i) with h | h
  · subst h; by_cases h7 : X[7] <;> simp [h7, BitVec.getElem_signExtend]
  · have k5 := (by decide : ∀ k (hk : k < 64), 1 ≤ k → (1#64)[k] = false) i hi h
    by_cases h7 : X[7] <;> simp [h7, k5, show i ≠ 0 by omega]

theorem bf_lsr51 (d x : BitVec 64) : evalBitfield .W64 .UBFM d x 51 63 = x >>> 51 := by
  unfold evalBitfield
  rfl

theorem tr19 : (BitVec.truncate 32 (19#64)).zeroExtend 64 = 19#64 := by decide

theorem movk_c : (18446744073709551312#64 &&& ~~~(65535#64 <<< 48)) ||| 127#64 <<< 48 =
    36028797018963664#64 := by decide

theorem xor_sel1 (a b : BitVec 64) (c : Bool) :
    (if c = true then a ^^^ b else 0#64) ^^^ a = if c = true then b else a := by
  cases c <;> simp

theorem xor_sel2 (a b : BitVec 64) (c : Bool) :
    (if c = true then a ^^^ b else 0#64) ^^^ b = if c = true then a else b := by
  cases c <;> simp

/-- Limbs of `FieldElement51::negate` (`16 p - d`, weakly reduced). -/
def nd0 (d0 d4 : BitVec 64) : BitVec 64 :=
  (36028797018963664#64 - d0 &&& 2251799813685247#64) +
    BitVec.zeroExtend 64 (BitVec.truncate 32 ((36028797018963952#64 - d4) >>> 51)) * 19#64
def nd1 (d1 d0 : BitVec 64) : BitVec 64 :=
  (36028797018963952#64 - d1 &&& 2251799813685247#64) + (36028797018963664#64 - d0) >>> 51
def ndk (dk dk1 : BitVec 64) : BitVec 64 :=
  (36028797018963952#64 - dk &&& 2251799813685247#64) + (36028797018963952#64 - dk1) >>> 51

/-- The stack words of block 6's frame `S` that stay fixed after the prologue: the 32-bit words of
the digit, the out pointer, and the saved callee-saved registers of the caller `sv`. -/
def Fx (m : Memory) (S X : BitVec 64) (sv : BitVec 5 → BitVec 64) : Prop :=
  m.read32 (S + 4#64) = sxtbW X ∧ m.read64 (S + 8#64) = sv 0#5 ∧
  m.read32 (S + 16#64) = signW X + sxtbW X ∧ m.read32 (S + 20#64) = signW X ∧
  m.read64 (S + 80#64) = sv 29#5 ∧ m.read64 (S + 88#64) = sv 30#5 ∧
  m.read64 (S + 96#64) = sv 28#5 ∧ m.read64 (S + 104#64) = sv 27#5 ∧
  m.read64 (S + 112#64) = sv 26#5 ∧ m.read64 (S + 120#64) = sv 25#5 ∧
  m.read64 (S + 128#64) = sv 24#5 ∧ m.read64 (S + 136#64) = sv 23#5 ∧
  m.read64 (S + 144#64) = sv 22#5 ∧ m.read64 (S + 152#64) = sv 21#5 ∧
  m.read64 (S + 160#64) = sv 20#5 ∧ m.read64 (S + 168#64) = sv 19#5

/-- The seven accumulator limbs kept in stack slots (`yp1, yp2, yp3, yp4, ym2, ym3, ym4`). -/
def Acc (m : Memory) (S a1 a2 a3 a4 a7 a8 a9 : BitVec 64) : Prop :=
  m.read64 (S + 32#64) = a1 ∧ m.read64 (S + 24#64) = a2 ∧ m.read64 (S + 56#64) = a3 ∧
  m.read64 (S + 48#64) = a4 ∧ m.read64 (S + 40#64) = a7 ∧ m.read64 (S + 64#64) = a8 ∧
  m.read64 (S + 72#64) = a9

end X25519Dalek.ESel
end

section
/-! # Block 6, offsets 0-108: the prologue (generated by tools/mk_pro.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace X25519Dalek.ESel

open Arm64 Arm64.Obj

theorem pro_run {mpl : MultiPlacement} {P : State → Prop} {s : State} {S : BitVec 64}
    {m0 : Memory} {ps : PState} {W : BitVec 64 → Prop}
    (hCL : (prog mpl 6).CodeLoaded m0) (hrun : s.status = .Running) (hW : WOwned m0 W)
    (hsp : S.toNat % 16 = 0)
    (hstk : ∀ c : BitVec 64, c.toNat + 8 ≤ 176 → AllB W (S + c) 8)
    (hstk2 : ∀ c1 c2 : BitVec 64, (c1 + c2).toNat + 8 ≤ 176 → AllB W (S + c1 + c2) 8)
    (hstk3 : ∀ c1 c2 c3 : BitVec 64, (c1 + c2 + c3).toNat + 8 ≤ 176 → AllB W (S + c1 + c2 + c3) 8)
    {sv : BitVec 5 → BitVec 64}
    (h : ∀ (r' : BitVec 5 → BitVec 64) (m' : Memory), MemOK m0 W m' → Fx m' S (sv 2#5) sv →
      Acc m' S 0#64 0#64 0#64 0#64 0#64 0#64 0#64 →
      r' 19#5 = 0#64 → r' 20#5 = 0#64 → r' 21#5 = 1#64 → r' 22#5 = 0#64 → r' 23#5 = 1#64 →
      r' 24#5 = 0#64 → r' 25#5 = sv 1#5 + 56#64 → r' 26#5 = 1#64 → r' 27#5 = 0#64 →
      r' 28#5 = 0#64 → r' 29#5 = S + 80#64 →
      Reach mpl 6 P (mkS s (mpl.base 6 + BitVec.ofNat 64 112) r' S m' ps)) :
    Reach mpl 6 P (mkS s (mpl.base 6 + BitVec.ofNat 64 0) (regL [sv 0#5, sv 1#5, sv 2#5, sv 3#5, sv 4#5, sv 5#5, sv 6#5, sv 7#5, sv 8#5, sv 9#5, sv 10#5, sv 11#5, sv 12#5, sv 13#5, sv 14#5, sv 15#5, sv 16#5, sv 17#5, sv 18#5, sv 19#5, sv 20#5, sv 21#5, sv 22#5, sv 23#5, sv 24#5, sv 25#5, sv 26#5, sv 27#5, sv 28#5, sv 29#5, sv 30#5, sv 31#5]) (S + 176#64) m0 ps) := by
  have hok := memOK_refl m0 W
  refine r_subsp hrun hW hok (f06_0 hCL) ?_
  simp only [Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, BitVec.add_sub_cancel]
  refine r_stp_sp ne31_29 ne31_30 hsp hrun hW hok (f06_4 hCL) (hstk _ (by decide)) (hstk2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_29, regL_get_30, regL_set_29, regL_set_30, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32] at hok ⊢
  refine r_stp_sp ne31_28 ne31_27 hsp hrun hW hok (f06_8 hCL) (hstk _ (by decide)) (hstk2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_27, regL_get_28, regL_set_27, regL_set_28, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32] at hok ⊢
  refine r_stp_sp ne31_26 ne31_25 hsp hrun hW hok (f06_12 hCL) (hstk _ (by decide)) (hstk2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_25, regL_get_26, regL_set_25, regL_set_26, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32] at hok ⊢
  refine r_stp_sp ne31_24 ne31_23 hsp hrun hW hok (f06_16 hCL) (hstk _ (by decide)) (hstk2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_23, regL_get_24, regL_set_23, regL_set_24, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32] at hok ⊢
  refine r_stp_sp ne31_22 ne31_21 hsp hrun hW hok (f06_20 hCL) (hstk _ (by decide)) (hstk2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_21, regL_get_22, regL_set_21, regL_set_22, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32] at hok ⊢
  refine r_stp_sp ne31_20 ne31_19 hsp hrun hW hok (f06_24 hCL) (hstk _ (by decide)) (hstk2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_19, regL_get_20, regL_set_19, regL_set_20, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32] at hok ⊢
  refine r_add_gsp ne31_29 hrun hW hok (f06_28 hCL) ?_
  simp only [regL_get_29, regL_set_29, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_bfm32 ne31_8 ne31_2 hrun hW hok (f06_32 hCL) ?_
  simp only [regL_get_2, regL_get_8, regL_set_2, regL_set_8, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32]
  refine r_bfm32 ne31_9 ne31_2 hrun hW hok (f06_36 hCL) ?_
  simp only [regL_get_2, regL_get_9, regL_set_2, regL_set_9, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32]
  refine r_movzz ne31_22 hrun hW hok (f06_40 hCL) ?_
  simp only [regL_get_22, regL_set_22, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_movzz ne31_27 hrun hW hok (f06_44 hCL) ?_
  simp only [regL_get_27, regL_set_27, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_movzz ne31_28 hrun hW hok (f06_48 hCL) ?_
  simp only [regL_get_28, regL_set_28, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_movzz ne31_19 hrun hW hok (f06_52 hCL) ?_
  simp only [regL_get_19, regL_set_19, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_movzz ne31_20 hrun hW hok (f06_56 hCL) ?_
  simp only [regL_get_20, regL_set_20, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_movzz ne31_24 hrun hW hok (f06_60 hCL) ?_
  simp only [regL_get_24, regL_set_24, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_str32_sp ne31_8 hsp hrun hW hok (f06_64 hCL) (allB_mono (hstk _ (by decide)) (by decide)) (fun hok => ?_)
  simp only [regL_get_8, regL_set_8, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32] at hok ⊢
  refine r_add32 ne31_8 ne31_9 ne31_8 hrun hW hok (f06_68 hCL) ?_
  simp only [regL_get_8, regL_get_9, regL_set_8, regL_set_9, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32]
  refine r_addi ne31_25 ne31_1 hrun hW hok (f06_72 hCL) ?_
  simp only [regL_get_1, regL_get_25, regL_set_1, regL_set_25, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_movz ne31_26 hrun hW hok (f06_76 hCL) ?_
  simp only [regL_get_26, regL_set_26, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_movz ne31_21 hrun hW hok (f06_80 hCL) ?_
  simp only [regL_get_21, regL_set_21, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_movz ne31_23 hrun hW hok (f06_84 hCL) ?_
  simp only [regL_get_23, regL_set_23, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_str_sp ne31_0 hsp hrun hW hok (f06_88 hCL) (hstk _ (by decide)) (fun hok => ?_)
  simp only [regL_get_0, regL_set_0, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32] at hok ⊢
  refine r_stpzz_sp hsp hrun hW hok (f06_92 hCL) (hstk _ (by decide)) (hstk2 _ _ (by decide)) (fun hok => ?_)
  simp only [Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32] at hok ⊢
  refine r_stpzz_g ne31_29 hrun hW hok (f06_96 hCL) (hstk2 _ _ (by decide)) (hstk3 _ _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_29, regL_set_29, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32] at hok ⊢
  refine r_strz_sp hsp hrun hW hok (f06_100 hCL) (hstk _ (by decide)) (fun hok => ?_)
  simp only [Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32] at hok ⊢
  refine r_stpzz_g ne31_29 hrun hW hok (f06_104 hCL) (hstk2 _ _ (by decide)) (hstk3 _ _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_29, regL_set_29, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32] at hok ⊢
  refine r_stp32_sp ne31_8 ne31_9 hsp hrun hW hok (f06_108 hCL) (allB_mono (hstk _ (by decide)) (by decide)) (allB_mono (hstk2 _ _ (by decide)) (by decide)) (fun hok => ?_)
  simp only [regL_get_8, regL_get_9, regL_set_8, regL_set_9, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, bf_sxtb, bf_sign, tz32] at hok ⊢
  refine h _ _ hok ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  all_goals simp only [read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow]

end X25519Dalek.ESel
end

section
/-! # Block 6, the loop body: offsets 112-128 and 136-416 (generated by tools/mk_loop.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace X25519Dalek.ESel

open Arm64 Arm64.Obj

theorem pre_run {mpl : MultiPlacement} {P : State → Prop} {s : State} {S : BitVec 64}
    {m0 m : Memory} {ps : PState} {W : BitVec 64 → Prop}
    (hCL : (prog mpl 6).CodeLoaded m0) (hrun : s.status = .Running) (hW : WOwned m0 W)
    (hok : MemOK m0 W m) (hsp : S.toNat % 16 = 0)
    (hR1 : ∀ c : BitVec 64, c.toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c) 8)
    (hR2 : ∀ c1 c2 : BitVec 64, (c1 + c2).toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c1 + c2) 8)
    {w16 w20 : BitVec 32} {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 : BitVec 64}
    (hm16 : m.read32 (S + 16#64) = w16) (hm20 : m.read32 (S + 20#64) = w20)
    (h : ∀ (a8 a9 : BitVec 64) (ps' : PState), Reach mpl 6 P (mkS s (mpl.base 6 + BitVec.ofNat 64 132)
      (regL [if CZ w16 w20 q26 then 1#64 else 0#64, q1, q2, q3, q4, q5, q6, q7, a8, a9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) S m ps')) :
    Reach mpl 6 P (mkS s (mpl.base 6 + BitVec.ofNat 64 112) (regL [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) S m ps) := by
  refine r_ldp32_sp ne31_8 ne31_9 hsp hrun hW hok (f06_112 hCL) (canRead_of hok (allB_mono (hR1 _ (by decide)) (by decide))) (canRead_of hok (allB_mono (hR2 _ _ (by decide)) (by decide))) (fun v112a v112b e112a e112b => ?_)
  simp only [regL_get_8, regL_get_9, regL_set_8, regL_set_9, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, tz32, tz16, tr_ffff, hm16, hm20] at e112a e112b ⊢
  subst v112a v112b
  refine r_eor32 ne31_8 ne31_8 ne31_26 hrun hW hok (f06_116 hCL) ?_
  simp only [regL_get_8, regL_get_26, regL_set_8, regL_set_26, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, tz32, tz16, tr_ffff]
  refine r_andi32 ne31_8 ne31_8 hrun hW hok (f06_120 hCL) ?_
  simp only [regL_get_8, regL_set_8, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, tz32, tz16, tr_ffff]
  refine r_cmp_uxth ne31_8 ne31_9 hrun hW hok (f06_124 hCL) ?_
  simp only [regL_get_8, regL_get_9, regL_set_8, regL_set_9, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, tz32, tz16, tr_ffff]
  refine r_cset_eq ne31_0 hrun hW hok (f06_128 hCL) ?_
  simp only [regL_get_0, regL_set_0, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, tz32, tz16, tr_ffff]
  exact h _ _ _

theorem body_run {mpl : MultiPlacement} {P : State → Prop} {s : State} {S : BitVec 64}
    {m0 m : Memory} {ps : PState} {W : BitVec 64 → Prop}
    (hCL : (prog mpl 6).CodeLoaded m0) (hrun : s.status = .Running) (hW : WOwned m0 W)
    (hok : MemOK m0 W m) (hsp : S.toNat % 16 = 0)
    (hstk : ∀ c : BitVec 64, (24 ≤ c.toNat ∧ c.toNat + 8 ≤ 80) → AllB W (S + c) 8)
    (hstk2 : ∀ c1 c2 : BitVec 64, (24 ≤ (c1 + c2).toNat ∧ (c1 + c2).toNat + 8 ≤ 80) → AllB W (S + c1 + c2) 8)
    (hR1 : ∀ c : BitVec 64, c.toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c) 8)
    (hR2 : ∀ c1 c2 : BitVec 64, (c1 + c2).toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c1 + c2) 8)
    (hR3 : ∀ c1 c2 c3 : BitVec 64, (c1 + c2 + c3).toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c1 + c2 + c3) 8)
    {B25 J : BitVec 64}
    (hcrT : ∀ m', MemOK m0 W m' → ∀ c : BitVec 64, (c + 56#64).toNat + 8 ≤ 120 → m'.canRead (B25 + c) 8 = true)
    (hcrT2 : ∀ m', MemOK m0 W m' → ∀ c : BitVec 64, (c + 64#64).toNat + 8 ≤ 120 →
      m'.canRead (B25 + c + 8#64) 8 = true)
    {t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : BitVec 64} {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q30 q31 : BitVec 64} {c : Bool}
    (hT0 : ∀ m', MemOK m0 W m' → m'.read64 (B25 + 0xffffffffffffffc8#64) = t0)
    (hT1 : ∀ m', MemOK m0 W m' → m'.read64 (B25 + 0xffffffffffffffd0#64) = t1)
    (hT2 : ∀ m', MemOK m0 W m' → m'.read64 (B25 + 0xffffffffffffffd8#64) = t2)
    (hT3 : ∀ m', MemOK m0 W m' → m'.read64 (B25 + 0xffffffffffffffe0#64) = t3)
    (hT4 : ∀ m', MemOK m0 W m' → m'.read64 (B25 + 0xffffffffffffffe8#64) = t4)
    (hT5 : ∀ m', MemOK m0 W m' → m'.read64 (B25 + 0xfffffffffffffff0#64) = t5)
    (hT6 : ∀ m', MemOK m0 W m' → m'.read64 (B25 + 0xfffffffffffffff8#64) = t6)
    (hT7 : ∀ m', MemOK m0 W m' → m'.read64 B25 = t7)
    (hT8 : ∀ m', MemOK m0 W m' → m'.read64 (B25 + 8#64) = t8)
    (hT9 : ∀ m', MemOK m0 W m' → m'.read64 (B25 + 16#64) = t9)
    (hT10 : ∀ m', MemOK m0 W m' → m'.read64 (B25 + 24#64) = t10)
    (hT11 : ∀ m', MemOK m0 W m' → m'.read64 (B25 + 32#64) = t11)
    (hT12 : ∀ m', MemOK m0 W m' → m'.read64 (B25 + 40#64) = t12)
    (hT13 : ∀ m', MemOK m0 W m' → m'.read64 (B25 + 48#64) = t13)
    (hT14 : ∀ m', MemOK m0 W m' → m'.read64 (B25 + 56#64) = t14)
    (hacc : Acc m S a1 a2 a3 a4 a7 a8 a9)
    (hq0 : q0 &&& 255#64 = if c = true then 1#64 else 0#64)
    (h : ∀ (m' : Memory) (L' : List (BitVec 64)) (ps' : PState), MemOK m0 W m' →
      ps'.z = decide (J + 1#64 = 9#64) →
      Acc m' S (if c then t1 else a1) (if c then t2 else a2) (if c then t3 else a3) (if c then t4 else a4)
        (if c then t7 else a7) (if c then t8 else a8) (if c then t9 else a9) →
      regL L' 19#5 = (if c then t12 else a12) → regL L' 20#5 = (if c then t11 else a11) →
      regL L' 21#5 = (if c then t0 else a0) → regL L' 22#5 = (if c then t6 else a6) →
      regL L' 23#5 = (if c then t5 else a5) → regL L' 24#5 = (if c then t10 else a10) →
      regL L' 25#5 = B25 + 120#64 → regL L' 26#5 = J + 1#64 →
      regL L' 27#5 = (if c then t14 else a14) → regL L' 28#5 = (if c then t13 else a13) →
      regL L' 29#5 = S + 80#64 →
      Reach mpl 6 P (mkS s (mpl.base 6 + BitVec.ofNat 64 420) (regL L') S m' ps')) :
    Reach mpl 6 P (mkS s (mpl.base 6 + BitVec.ofNat 64 136) (regL [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, a12, a11, a0, a6, a5, a10, B25, J, a14, a13, S + 80#64, q30, q31]) S m ps) := by
  obtain ⟨hA1, hA2, hA3, hA4, hA7, hA8, hA9⟩ := hacc
  refine r_ldp_g ne31_10 ne31_11 ne31_25 hrun hW hok (f06_136 hCL) (hcrT _ hok _ (by decide)) (hcrT2 _ hok _ (by decide)) (fun v136a v136b e136a e136b => ?_)
  simp only [regL_get_10, regL_get_11, regL_get_25, regL_set_10, regL_set_11, regL_set_25, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hA1, hA2, hA3, hA4, hA7, hA8, hA9, hT0 _ hok, hT1 _ hok, hT2 _ hok, hT3 _ hok, hT4 _ hok, hT5 _ hok, hT6 _ hok, hT7 _ hok, hT8 _ hok, hT9 _ hok, hT10 _ hok, hT11 _ hok, hT12 _ hok, hT13 _ hok, hT14 _ hok] at e136a e136b ⊢
  subst v136a v136b
  refine r_andi ne31_9 ne31_0 hrun hW hok (f06_140 hCL) (fun v140 e140 => ?_)
  simp only [regL_get_0, regL_get_9, regL_set_0, regL_set_9, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m] at e140 ⊢
  subst v140
  refine r_ldp_sp ne31_14 ne31_13 hsp hrun hW hok (f06_144 hCL) (canRead_of hok (hR1 _ (by decide))) (canRead_of hok (hR2 _ _ (by decide))) (fun v144a v144b e144a e144b => ?_)
  simp only [regL_get_13, regL_get_14, regL_set_13, regL_set_14, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hA1, hA2, hA3, hA4, hA7, hA8, hA9, hT0 _ hok, hT1 _ hok, hT2 _ hok, hT3 _ hok, hT4 _ hok, hT5 _ hok, hT6 _ hok, hT7 _ hok, hT8 _ hok, hT9 _ hok, hT10 _ hok, hT11 _ hok, hT12 _ hok, hT13 _ hok, hT14 _ hok] at e144a e144b ⊢
  subst v144a v144b
  refine r_neg ne31_8 ne31_9 hrun hW hok (f06_148 hCL) ?_
  simp only [regL_get_8, regL_get_9, regL_set_8, regL_set_9, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_subi ne31_9 ne31_9 hrun hW hok (f06_152 hCL) ?_
  simp only [regL_get_9, regL_set_9, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_addi ne31_26 ne31_26 hrun hW hok (f06_156 hCL) ?_
  simp only [regL_get_26, regL_set_26, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_and ne31_12 ne31_21 ne31_9 hrun hW hok (f06_160 hCL) ?_
  simp only [regL_get_9, regL_get_12, regL_get_21, regL_set_9, regL_set_12, regL_set_21, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_10 ne31_10 ne31_8 hrun hW hok (f06_164 hCL) ?_
  simp only [regL_get_8, regL_get_10, regL_set_8, regL_set_10, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_11 ne31_11 ne31_8 hrun hW hok (f06_168 hCL) ?_
  simp only [regL_get_8, regL_get_11, regL_set_8, regL_set_11, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_orr ne31_21 ne31_10 ne31_12 hrun hW hok (f06_172 hCL) ?_
  simp only [regL_get_10, regL_get_12, regL_get_21, regL_set_10, regL_set_12, regL_set_21, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_ldp_g ne31_10 ne31_12 ne31_25 hrun hW hok (f06_176 hCL) (hcrT _ hok _ (by decide)) (hcrT2 _ hok _ (by decide)) (fun v176a v176b e176a e176b => ?_)
  simp only [regL_get_10, regL_get_12, regL_get_25, regL_set_10, regL_set_12, regL_set_25, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hA1, hA2, hA3, hA4, hA7, hA8, hA9, hT0 _ hok, hT1 _ hok, hT2 _ hok, hT3 _ hok, hT4 _ hok, hT5 _ hok, hT6 _ hok, hT7 _ hok, hT8 _ hok, hT9 _ hok, hT10 _ hok, hT11 _ hok, hT12 _ hok, hT13 _ hok, hT14 _ hok] at e176a e176b ⊢
  subst v176a v176b
  refine r_and ne31_13 ne31_13 ne31_9 hrun hW hok (f06_180 hCL) ?_
  simp only [regL_get_9, regL_get_13, regL_set_9, regL_set_13, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_14 ne31_14 ne31_9 hrun hW hok (f06_184 hCL) ?_
  simp only [regL_get_9, regL_get_14, regL_set_9, regL_set_14, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_cmpi ne31_26 hrun hW hok (f06_188 hCL) (fun ps188 hz188 => ?_)
  simp only [regL_get_26, regL_set_26, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot] at hz188 ⊢
  refine r_orr ne31_11 ne31_11 ne31_13 hrun hW hok (f06_192 hCL) ?_
  simp only [regL_get_11, regL_get_13, regL_set_11, regL_set_13, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_str_sp ne31_11 hsp hrun hW hok (f06_196 hCL) (hstk _ (by decide)) (fun hok => ?_)
  simp only [regL_get_11, regL_set_11, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m] at hok ⊢
  refine r_ldur_g ne31_11 ne31_29 hrun hW hok (f06_200 hCL) (canRead_of hok (hR2 _ _ (by decide))) (fun v200 e200 => ?_)
  simp only [regL_get_11, regL_get_29, regL_set_11, regL_set_29, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hA1, hA2, hA3, hA4, hA7, hA8, hA9, hT0 _ hok, hT1 _ hok, hT2 _ hok, hT3 _ hok, hT4 _ hok, hT5 _ hok, hT6 _ hok, hT7 _ hok, hT8 _ hok, hT9 _ hok, hT10 _ hok, hT11 _ hok, hT12 _ hok, hT13 _ hok, hT14 _ hok] at e200 ⊢
  subst v200
  refine r_and ne31_10 ne31_10 ne31_8 hrun hW hok (f06_204 hCL) ?_
  simp only [regL_get_8, regL_get_10, regL_set_8, regL_set_10, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_12 ne31_12 ne31_8 hrun hW hok (f06_208 hCL) ?_
  simp only [regL_get_8, regL_get_12, regL_set_8, regL_set_12, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_orr ne31_10 ne31_10 ne31_14 hrun hW hok (f06_212 hCL) ?_
  simp only [regL_get_10, regL_get_14, regL_set_10, regL_set_14, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_11 ne31_11 ne31_9 hrun hW hok (f06_216 hCL) ?_
  simp only [regL_get_9, regL_get_11, regL_set_9, regL_set_11, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_str_sp ne31_10 hsp hrun hW hok (f06_220 hCL) (hstk _ (by decide)) (fun hok => ?_)
  simp only [regL_get_10, regL_set_10, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m] at hok ⊢
  refine r_orr ne31_10 ne31_12 ne31_11 hrun hW hok (f06_224 hCL) ?_
  simp only [regL_get_10, regL_get_11, regL_get_12, regL_set_10, regL_set_11, regL_set_12, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_ldur_g ne31_11 ne31_29 hrun hW hok (f06_228 hCL) (canRead_of hok (hR2 _ _ (by decide))) (fun v228 e228 => ?_)
  simp only [regL_get_11, regL_get_29, regL_set_11, regL_set_29, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hA1, hA2, hA3, hA4, hA7, hA8, hA9, hT0 _ hok, hT1 _ hok, hT2 _ hok, hT3 _ hok, hT4 _ hok, hT5 _ hok, hT6 _ hok, hT7 _ hok, hT8 _ hok, hT9 _ hok, hT10 _ hok, hT11 _ hok, hT12 _ hok, hT13 _ hok, hT14 _ hok] at e228 ⊢
  subst v228
  refine r_stur_g ne31_10 ne31_29 hrun hW hok (f06_232 hCL) (hstk2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_10, regL_get_29, regL_set_10, regL_set_29, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m] at hok ⊢
  refine r_ldp_g ne31_13 ne31_10 ne31_25 hrun hW hok (f06_236 hCL) (hcrT _ hok _ (by decide)) (hcrT2 _ hok _ (by decide)) (fun v236a v236b e236a e236b => ?_)
  simp only [regL_get_10, regL_get_13, regL_get_25, regL_set_10, regL_set_13, regL_set_25, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hA1, hA2, hA3, hA4, hA7, hA8, hA9, hT0 _ hok, hT1 _ hok, hT2 _ hok, hT3 _ hok, hT4 _ hok, hT5 _ hok, hT6 _ hok, hT7 _ hok, hT8 _ hok, hT9 _ hok, hT10 _ hok, hT11 _ hok, hT12 _ hok, hT13 _ hok, hT14 _ hok] at e236a e236b ⊢
  subst v236a v236b
  refine r_and ne31_11 ne31_11 ne31_9 hrun hW hok (f06_240 hCL) ?_
  simp only [regL_get_9, regL_get_11, regL_set_9, regL_set_11, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_12 ne31_13 ne31_8 hrun hW hok (f06_244 hCL) ?_
  simp only [regL_get_8, regL_get_12, regL_get_13, regL_set_8, regL_set_12, regL_set_13, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_ldp_g ne31_13 ne31_14 ne31_25 hrun hW hok (f06_248 hCL) (hcrT _ hok _ (by decide)) (hcrT2 _ hok _ (by decide)) (fun v248a v248b e248a e248b => ?_)
  simp only [regL_get_13, regL_get_14, regL_get_25, regL_set_13, regL_set_14, regL_set_25, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hA1, hA2, hA3, hA4, hA7, hA8, hA9, hT0 _ hok, hT1 _ hok, hT2 _ hok, hT3 _ hok, hT4 _ hok, hT5 _ hok, hT6 _ hok, hT7 _ hok, hT8 _ hok, hT9 _ hok, hT10 _ hok, hT11 _ hok, hT12 _ hok, hT13 _ hok, hT14 _ hok] at e248a e248b ⊢
  subst v248a v248b
  refine r_orr ne31_11 ne31_12 ne31_11 hrun hW hok (f06_252 hCL) ?_
  simp only [regL_get_11, regL_get_12, regL_set_11, regL_set_12, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_10 ne31_10 ne31_8 hrun hW hok (f06_256 hCL) ?_
  simp only [regL_get_8, regL_get_10, regL_set_8, regL_set_10, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_12 ne31_22 ne31_9 hrun hW hok (f06_260 hCL) ?_
  simp only [regL_get_9, regL_get_12, regL_get_22, regL_set_9, regL_set_12, regL_set_22, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_stur_g ne31_11 ne31_29 hrun hW hok (f06_264 hCL) (hstk2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_11, regL_get_29, regL_set_11, regL_set_29, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m] at hok ⊢
  refine r_and ne31_11 ne31_23 ne31_9 hrun hW hok (f06_268 hCL) ?_
  simp only [regL_get_9, regL_get_11, regL_get_23, regL_set_9, regL_set_11, regL_set_23, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_orr ne31_23 ne31_10 ne31_11 hrun hW hok (f06_272 hCL) ?_
  simp only [regL_get_10, regL_get_11, regL_get_23, regL_set_10, regL_set_11, regL_set_23, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_ldr_sp ne31_11 hsp hrun hW hok (f06_276 hCL) (canRead_of hok (hR1 _ (by decide))) (fun v276 e276 => ?_)
  simp only [regL_get_11, regL_set_11, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hA1, hA2, hA3, hA4, hA7, hA8, hA9, hT0 _ hok, hT1 _ hok, hT2 _ hok, hT3 _ hok, hT4 _ hok, hT5 _ hok, hT6 _ hok, hT7 _ hok, hT8 _ hok, hT9 _ hok, hT10 _ hok, hT11 _ hok, hT12 _ hok, hT13 _ hok, hT14 _ hok] at e276 ⊢
  subst v276
  refine r_and ne31_13 ne31_13 ne31_8 hrun hW hok (f06_280 hCL) ?_
  simp only [regL_get_8, regL_get_13, regL_set_8, regL_set_13, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_orr ne31_22 ne31_13 ne31_12 hrun hW hok (f06_284 hCL) ?_
  simp only [regL_get_12, regL_get_13, regL_get_22, regL_set_12, regL_set_13, regL_set_22, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_12 ne31_14 ne31_8 hrun hW hok (f06_288 hCL) ?_
  simp only [regL_get_8, regL_get_12, regL_get_14, regL_set_8, regL_set_12, regL_set_14, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_11 ne31_11 ne31_9 hrun hW hok (f06_292 hCL) ?_
  simp only [regL_get_9, regL_get_11, regL_set_9, regL_set_11, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_ldp_g ne31_10 ne31_13 ne31_25 hrun hW hok (f06_296 hCL) (hcrT _ hok _ (by decide)) (hcrT2 _ hok _ (by decide)) (fun v296a v296b e296a e296b => ?_)
  simp only [regL_get_10, regL_get_13, regL_get_25, regL_set_10, regL_set_13, regL_set_25, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hA1, hA2, hA3, hA4, hA7, hA8, hA9, hT0 _ hok, hT1 _ hok, hT2 _ hok, hT3 _ hok, hT4 _ hok, hT5 _ hok, hT6 _ hok, hT7 _ hok, hT8 _ hok, hT9 _ hok, hT10 _ hok, hT11 _ hok, hT12 _ hok, hT13 _ hok, hT14 _ hok] at e296a e296b ⊢
  subst v296a v296b
  refine r_orr ne31_11 ne31_12 ne31_11 hrun hW hok (f06_300 hCL) ?_
  simp only [regL_get_11, regL_get_12, regL_set_11, regL_set_12, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_str_sp ne31_11 hsp hrun hW hok (f06_304 hCL) (hstk _ (by decide)) (fun hok => ?_)
  simp only [regL_get_11, regL_set_11, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m] at hok ⊢
  refine r_ldp_g ne31_11 ne31_12 ne31_29 hrun hW hok (f06_308 hCL) (canRead_of hok (hR2 _ _ (by decide))) (canRead_of hok (hR3 _ _ _ (by decide))) (fun v308a v308b e308a e308b => ?_)
  simp only [regL_get_11, regL_get_12, regL_get_29, regL_set_11, regL_set_12, regL_set_29, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hA1, hA2, hA3, hA4, hA7, hA8, hA9, hT0 _ hok, hT1 _ hok, hT2 _ hok, hT3 _ hok, hT4 _ hok, hT5 _ hok, hT6 _ hok, hT7 _ hok, hT8 _ hok, hT9 _ hok, hT10 _ hok, hT11 _ hok, hT12 _ hok, hT13 _ hok, hT14 _ hok] at e308a e308b ⊢
  subst v308a v308b
  refine r_and ne31_10 ne31_10 ne31_8 hrun hW hok (f06_312 hCL) ?_
  simp only [regL_get_8, regL_get_10, regL_set_8, regL_set_10, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_13 ne31_13 ne31_8 hrun hW hok (f06_316 hCL) ?_
  simp only [regL_get_8, regL_get_13, regL_set_8, regL_set_13, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_11 ne31_11 ne31_9 hrun hW hok (f06_320 hCL) ?_
  simp only [regL_get_9, regL_get_11, regL_set_9, regL_set_11, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_12 ne31_12 ne31_9 hrun hW hok (f06_324 hCL) ?_
  simp only [regL_get_9, regL_get_12, regL_set_9, regL_set_12, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_orr ne31_10 ne31_10 ne31_11 hrun hW hok (f06_328 hCL) ?_
  simp only [regL_get_10, regL_get_11, regL_set_10, regL_set_11, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_11 ne31_24 ne31_9 hrun hW hok (f06_332 hCL) ?_
  simp only [regL_get_9, regL_get_11, regL_get_24, regL_set_9, regL_set_11, regL_set_24, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_stur_g ne31_10 ne31_29 hrun hW hok (f06_336 hCL) (hstk2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_10, regL_get_29, regL_set_10, regL_set_29, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m] at hok ⊢
  refine r_orr ne31_10 ne31_13 ne31_12 hrun hW hok (f06_340 hCL) ?_
  simp only [regL_get_10, regL_get_12, regL_get_13, regL_set_10, regL_set_12, regL_set_13, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_stur_g ne31_10 ne31_29 hrun hW hok (f06_344 hCL) (hstk2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_10, regL_get_29, regL_set_10, regL_set_29, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m] at hok ⊢
  refine r_ldp_g ne31_14 ne31_10 ne31_25 hrun hW hok (f06_348 hCL) (hcrT _ hok _ (by decide)) (hcrT2 _ hok _ (by decide)) (fun v348a v348b e348a e348b => ?_)
  simp only [regL_get_10, regL_get_14, regL_get_25, regL_set_10, regL_set_14, regL_set_25, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hA1, hA2, hA3, hA4, hA7, hA8, hA9, hT0 _ hok, hT1 _ hok, hT2 _ hok, hT3 _ hok, hT4 _ hok, hT5 _ hok, hT6 _ hok, hT7 _ hok, hT8 _ hok, hT9 _ hok, hT10 _ hok, hT11 _ hok, hT12 _ hok, hT13 _ hok, hT14 _ hok] at e348a e348b ⊢
  subst v348a v348b
  refine r_and ne31_12 ne31_14 ne31_8 hrun hW hok (f06_352 hCL) ?_
  simp only [regL_get_8, regL_get_12, regL_get_14, regL_set_8, regL_set_12, regL_set_14, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_ldp_g ne31_13 ne31_14 ne31_25 hrun hW hok (f06_356 hCL) (hcrT _ hok _ (by decide)) (hcrT2 _ hok _ (by decide)) (fun v356a v356b e356a e356b => ?_)
  simp only [regL_get_13, regL_get_14, regL_get_25, regL_set_13, regL_set_14, regL_set_25, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hA1, hA2, hA3, hA4, hA7, hA8, hA9, hT0 _ hok, hT1 _ hok, hT2 _ hok, hT3 _ hok, hT4 _ hok, hT5 _ hok, hT6 _ hok, hT7 _ hok, hT8 _ hok, hT9 _ hok, hT10 _ hok, hT11 _ hok, hT12 _ hok, hT13 _ hok, hT14 _ hok] at e356a e356b ⊢
  subst v356a v356b
  refine r_orr ne31_24 ne31_12 ne31_11 hrun hW hok (f06_360 hCL) ?_
  simp only [regL_get_11, regL_get_12, regL_get_24, regL_set_11, regL_set_12, regL_set_24, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_11 ne31_20 ne31_9 hrun hW hok (f06_364 hCL) ?_
  simp only [regL_get_9, regL_get_11, regL_get_20, regL_set_9, regL_set_11, regL_set_20, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_10 ne31_10 ne31_8 hrun hW hok (f06_368 hCL) ?_
  simp only [regL_get_8, regL_get_10, regL_set_8, regL_set_10, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_orr ne31_20 ne31_10 ne31_11 hrun hW hok (f06_372 hCL) ?_
  simp only [regL_get_10, regL_get_11, regL_get_20, regL_set_10, regL_set_11, regL_set_20, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_ldr_g ne31_10 ne31_25 hrun hW hok (f06_376 hCL) (hcrT _ hok _ (by decide)) (fun v376 e376 => ?_)
  simp only [regL_get_10, regL_get_25, regL_set_10, regL_set_25, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hA1, hA2, hA3, hA4, hA7, hA8, hA9, hT0 _ hok, hT1 _ hok, hT2 _ hok, hT3 _ hok, hT4 _ hok, hT5 _ hok, hT6 _ hok, hT7 _ hok, hT8 _ hok, hT9 _ hok, hT10 _ hok, hT11 _ hok, hT12 _ hok, hT13 _ hok, hT14 _ hok] at e376 ⊢
  subst v376
  refine r_and ne31_12 ne31_19 ne31_9 hrun hW hok (f06_380 hCL) ?_
  simp only [regL_get_9, regL_get_12, regL_get_19, regL_set_9, regL_set_12, regL_set_19, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_13 ne31_13 ne31_8 hrun hW hok (f06_384 hCL) ?_
  simp only [regL_get_8, regL_get_13, regL_set_8, regL_set_13, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_11 ne31_28 ne31_9 hrun hW hok (f06_388 hCL) ?_
  simp only [regL_get_9, regL_get_11, regL_get_28, regL_set_9, regL_set_11, regL_set_28, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_9 ne31_27 ne31_9 hrun hW hok (f06_392 hCL) ?_
  simp only [regL_get_9, regL_get_27, regL_set_9, regL_set_27, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_orr ne31_19 ne31_13 ne31_12 hrun hW hok (f06_396 hCL) ?_
  simp only [regL_get_12, regL_get_13, regL_get_19, regL_set_12, regL_set_13, regL_set_19, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_12 ne31_14 ne31_8 hrun hW hok (f06_400 hCL) ?_
  simp only [regL_get_8, regL_get_12, regL_get_14, regL_set_8, regL_set_12, regL_set_14, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_and ne31_8 ne31_10 ne31_8 hrun hW hok (f06_404 hCL) ?_
  simp only [regL_get_8, regL_get_10, regL_set_8, regL_set_10, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_orr ne31_28 ne31_12 ne31_11 hrun hW hok (f06_408 hCL) ?_
  simp only [regL_get_11, regL_get_12, regL_get_28, regL_set_11, regL_set_12, regL_set_28, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_orr ne31_27 ne31_8 ne31_9 hrun hW hok (f06_412 hCL) ?_
  simp only [regL_get_8, regL_get_9, regL_get_27, regL_set_8, regL_set_9, regL_set_27, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m]
  refine r_addi ne31_25 ne31_25 hrun hW hok (f06_416 hCL) ?_
  simp only [regL_get_25, regL_set_25, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine h _ _ _ hok hz188 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  all_goals simp only [read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow]

end X25519Dalek.ESel
end

section
/-! # Block 6, the epilogue: offsets 424-428 and 436-760 (generated by tools/mk_epi.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace X25519Dalek.ESel

open Arm64 Arm64.Obj

theorem pre2_run {mpl : MultiPlacement} {P : State → Prop} {s : State} {S : BitVec 64}
    {m0 m : Memory} {ps : PState} {W : BitVec 64 → Prop}
    (hCL : (prog mpl 6).CodeLoaded m0) (hrun : s.status = .Running) (hW : WOwned m0 W)
    (hok : MemOK m0 W m) (hsp : S.toNat % 16 = 0)
    (hR1 : ∀ c : BitVec 64, c.toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c) 8)
    (hR2 : ∀ c1 c2 : BitVec 64, (c1 + c2).toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c1 + c2) 8)
    (hR3 : ∀ c1 c2 c3 : BitVec 64, (c1 + c2 + c3).toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c1 + c2 + c3) 8)
    {X : BitVec 64} {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 : BitVec 64}
    (hm4 : m.read32 (S + 4#64) = sxtbW X)
    (h : ∀ (a8 : BitVec 64), Reach mpl 6 P (mkS s (mpl.base 6 + BitVec.ofNat 64 432)
      (regL [if X.getLsbD 7 = true then 1#64 else 0#64, q1, q2, q3, q4, q5, q6, q7, a8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) S m ps)) :
    Reach mpl 6 P (mkS s (mpl.base 6 + BitVec.ofNat 64 424) (regL [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) S m ps) := by
  refine r_ldr32_sp ne31_8 hsp hrun hW hok (f06_424 hCL) (canRead_of hok (allB_mono (hR1 _ (by decide)) (by decide))) (fun v424 e424 => ?_)
  simp only [regL_get_8, regL_set_8, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, tz32, bf_bit7, hm4] at e424 ⊢
  subst v424
  refine r_bfm32 ne31_0 ne31_8 hrun hW hok (f06_428 hCL) ?_
  simp only [regL_get_0, regL_get_8, regL_set_0, regL_set_8, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, tz32, bf_bit7]
  exact h _

theorem epiA_run {mpl : MultiPlacement} {P : State → Prop} {s : State} {S : BitVec 64}
    {m0 m : Memory} {ps : PState} {W : BitVec 64 → Prop}
    (hCL : (prog mpl 6).CodeLoaded m0) (hrun : s.status = .Running) (hW : WOwned m0 W)
    (hok : MemOK m0 W m) (hsp : S.toNat % 16 = 0)
    (hR1 : ∀ c : BitVec 64, c.toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c) 8)
    (hR2 : ∀ c1 c2 : BitVec 64, (c1 + c2).toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c1 + c2) 8)
    (hR3 : ∀ c1 c2 c3 : BitVec 64, (c1 + c2 + c3).toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c1 + c2 + c3) 8)
    {o : BitVec 64} {sv : BitVec 5 → BitVec 64}
    (hout : ∀ c : BitVec 64, c.toNat + 8 ≤ 120 → AllB W (o + c) 8)
    (hout2 : ∀ c1 c2 : BitVec 64, (c1 + c2).toNat + 8 ≤ 120 → AllB W (o + c1 + c2) 8) {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : BitVec 64}
    {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q25 q26 q30 q31 : BitVec 64} {c : Bool}
    (hS8 : ∀ m', MemOK m0 W m' → m'.read64 (S + 8#64) = o)
    (hS24 : ∀ m', MemOK m0 W m' → m'.read64 (S + 24#64) = a2)
    (hS32 : ∀ m', MemOK m0 W m' → m'.read64 (S + 32#64) = a1)
    (hS40 : ∀ m', MemOK m0 W m' → m'.read64 (S + 40#64) = a7)
    (hS48 : ∀ m', MemOK m0 W m' → m'.read64 (S + 48#64) = a4)
    (hS56 : ∀ m', MemOK m0 W m' → m'.read64 (S + 56#64) = a3)
    (hS64 : ∀ m', MemOK m0 W m' → m'.read64 (S + 64#64) = a8)
    (hS72 : ∀ m', MemOK m0 W m' → m'.read64 (S + 72#64) = a9)
    (hS80 : ∀ m', MemOK m0 W m' → m'.read64 (S + 80#64) = sv 29#5)
    (hS88 : ∀ m', MemOK m0 W m' → m'.read64 (S + 88#64) = sv 30#5)
    (hS96 : ∀ m', MemOK m0 W m' → m'.read64 (S + 96#64) = sv 28#5)
    (hS104 : ∀ m', MemOK m0 W m' → m'.read64 (S + 104#64) = sv 27#5)
    (hS112 : ∀ m', MemOK m0 W m' → m'.read64 (S + 112#64) = sv 26#5)
    (hS120 : ∀ m', MemOK m0 W m' → m'.read64 (S + 120#64) = sv 25#5)
    (hS128 : ∀ m', MemOK m0 W m' → m'.read64 (S + 128#64) = sv 24#5)
    (hS136 : ∀ m', MemOK m0 W m' → m'.read64 (S + 136#64) = sv 23#5)
    (hS144 : ∀ m', MemOK m0 W m' → m'.read64 (S + 144#64) = sv 22#5)
    (hS152 : ∀ m', MemOK m0 W m' → m'.read64 (S + 152#64) = sv 21#5)
    (hS160 : ∀ m', MemOK m0 W m' → m'.read64 (S + 160#64) = sv 20#5)
    (hS168 : ∀ m', MemOK m0 W m' → m'.read64 (S + 168#64) = sv 19#5)
    (hq0 : q0 &&& 255#64 = if c = true then 1#64 else 0#64)
    (h : Reach mpl 6 P (mkS s (mpl.base 6 + BitVec.ofNat 64 596) (regL [if c = true then a6 else a1, a2, a3 ^^^ a8, a4 ^^^ a9, o, a6, a3, a4, (36028797018963952#64 - a14 &&& 2251799813685247#64) + (36028797018963952#64 - a13) >>> 51, if c = true then 18446744073709551615#64 else 0#64, (36028797018963952#64 - a12 &&& 2251799813685247#64) + (36028797018963952#64 - a11) >>> 51, (36028797018963952#64 - a13 &&& 2251799813685247#64) + (36028797018963952#64 - a12) >>> 51, (36028797018963952#64 - a11 &&& 2251799813685247#64) + (36028797018963664#64 - a10) >>> 51, (36028797018963664#64 - a10 &&& 2251799813685247#64) + BitVec.zeroExtend 64 (BitVec.truncate 32 ((36028797018963952#64 - a14) >>> 51)) * 19#64, if c = true then 1#64 else 0#64, if c = true then a0 ^^^ a5 else 0#64, if c = true then a1 ^^^ a6 else 0#64, if c = true then a2 ^^^ a7 else 0#64, if c = true then a5 else a0, a12, a11, a9, a7, a8, a10, a5, q26, a14, a13, S + 80#64, q30, q31]) S m ps)) :
    Reach mpl 6 P (mkS s (mpl.base 6 + BitVec.ofNat 64 436) (regL [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, a12, a11, a0, a6, a5, a10, q25, q26, a14, a13, S + 80#64, q30, q31]) S m ps) := by
  refine r_movn ne31_8 hrun hW hok (f06_436 hCL) ?_
  simp only [regL_get_8, regL_set_8, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_orri_z ne31_9 hrun hW hok (f06_440 hCL) ?_
  simp only [regL_get_9, regL_set_9, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_movz ne31_17 hrun hW hok (f06_444 hCL) ?_
  simp only [regL_get_17, regL_set_17, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_movk48 ne31_8 hrun hW hok (f06_448 hCL) ?_
  simp only [regL_get_8, regL_set_8, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_sub ne31_12 ne31_9 ne31_27 hrun hW hok (f06_452 hCL) ?_
  simp only [regL_get_9, regL_get_12, regL_get_27, regL_set_9, regL_set_12, regL_set_27, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_sub ne31_10 ne31_9 ne31_20 hrun hW hok (f06_456 hCL) ?_
  simp only [regL_get_9, regL_get_10, regL_get_20, regL_set_9, regL_set_10, regL_set_20, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_sub ne31_8 ne31_8 ne31_24 hrun hW hok (f06_460 hCL) ?_
  simp only [regL_get_8, regL_get_24, regL_set_8, regL_set_24, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_bfm64 ne31_13 ne31_12 hrun hW hok (f06_464 hCL) ?_
  simp only [regL_get_12, regL_get_13, regL_set_12, regL_set_13, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_sub ne31_11 ne31_9 ne31_19 hrun hW hok (f06_468 hCL) ?_
  simp only [regL_get_9, regL_get_11, regL_get_19, regL_set_9, regL_set_11, regL_set_19, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_sub ne31_9 ne31_9 ne31_28 hrun hW hok (f06_472 hCL) ?_
  simp only [regL_get_9, regL_get_28, regL_set_9, regL_set_28, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_andi ne31_14 ne31_8 hrun hW hok (f06_476 hCL) (fun v476 e476 => ?_)
  simp only [regL_get_8, regL_get_14, regL_set_8, regL_set_14, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c] at e476 ⊢
  subst v476
  refine r_andi ne31_15 ne31_10 hrun hW hok (f06_480 hCL) (fun v480 e480 => ?_)
  simp only [regL_get_10, regL_get_15, regL_set_10, regL_set_15, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c] at e480 ⊢
  subst v480
  refine r_andi ne31_1 ne31_12 hrun hW hok (f06_484 hCL) (fun v484 e484 => ?_)
  simp only [regL_get_1, regL_get_12, regL_set_1, regL_set_12, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c] at e484 ⊢
  subst v484
  refine r_umaddl ne31_13 ne31_13 ne31_17 ne31_14 hrun hW hok (f06_488 hCL) ?_
  simp only [regL_get_13, regL_get_14, regL_get_17, regL_set_13, regL_set_14, regL_set_17, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_add_lsr ne31_12 ne31_15 ne31_8 hrun hW hok (f06_492 hCL) (fun v492 e492 => ?_)
  simp only [regL_get_8, regL_get_12, regL_get_15, regL_set_8, regL_set_12, regL_set_15, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot] at e492 ⊢
  subst v492
  refine r_andi ne31_14 ne31_0 hrun hW hok (f06_496 hCL) (fun v496 e496 => ?_)
  simp only [regL_get_0, regL_get_14, regL_set_0, regL_set_14, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c] at e496 ⊢
  subst v496
  refine r_add_lsr ne31_8 ne31_1 ne31_9 hrun hW hok (f06_500 hCL) (fun v500 e500 => ?_)
  simp only [regL_get_1, regL_get_8, regL_get_9, regL_set_1, regL_set_8, regL_set_9, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot] at e500 ⊢
  subst v500
  refine r_andi ne31_18 ne31_9 hrun hW hok (f06_504 hCL) (fun v504 e504 => ?_)
  simp only [regL_get_9, regL_get_18, regL_set_9, regL_set_18, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c] at e504 ⊢
  subst v504
  refine r_ldp_sp ne31_1 ne31_0 hsp hrun hW hok (f06_508 hCL) (canRead_of hok (hR1 _ (by decide))) (canRead_of hok (hR2 _ _ (by decide))) (fun v508a v508b e508a e508b => ?_)
  simp only [regL_get_0, regL_get_1, regL_set_0, regL_set_1, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, far_add_left_iff, far_add_right_iff, hS8 _ hok, hS24 _ hok, hS32 _ hok, hS40 _ hok, hS48 _ hok, hS56 _ hok, hS64 _ hok, hS72 _ hok, hS80 _ hok, hS88 _ hok, hS96 _ hok, hS104 _ hok, hS112 _ hok, hS120 _ hok, hS128 _ hok, hS136 _ hok, hS144 _ hok, hS152 _ hok, hS160 _ hok, hS168 _ hok] at e508a e508b ⊢
  subst v508a v508b
  refine r_neg ne31_9 ne31_14 hrun hW hok (f06_512 hCL) ?_
  simp only [regL_get_9, regL_get_14, regL_set_9, regL_set_14, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_eor ne31_15 ne31_21 ne31_23 hrun hW hok (f06_516 hCL) ?_
  simp only [regL_get_15, regL_get_21, regL_get_23, regL_set_15, regL_set_21, regL_set_23, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_andi ne31_16 ne31_11 hrun hW hok (f06_520 hCL) (fun v520 e520 => ?_)
  simp only [regL_get_11, regL_get_16, regL_set_11, regL_set_16, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c] at e520 ⊢
  subst v520
  refine r_movx ne31_25 ne31_23 hrun hW hok (f06_524 hCL) ?_
  simp only [regL_get_23, regL_get_25, regL_set_23, regL_set_25, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_and ne31_15 ne31_15 ne31_9 hrun hW hok (f06_528 hCL) ?_
  simp only [regL_get_9, regL_get_15, regL_set_9, regL_set_15, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_ldp_g ne31_6 ne31_23 ne31_29 hrun hW hok (f06_532 hCL) (canRead_of hok (hR2 _ _ (by decide))) (canRead_of hok (hR3 _ _ _ (by decide))) (fun v532a v532b e532a e532b => ?_)
  simp only [regL_get_6, regL_get_23, regL_get_29, regL_set_6, regL_set_23, regL_set_29, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, far_add_left_iff, far_add_right_iff, hS8 _ hok, hS24 _ hok, hS32 _ hok, hS40 _ hok, hS48 _ hok, hS56 _ hok, hS64 _ hok, hS72 _ hok, hS80 _ hok, hS88 _ hok, hS96 _ hok, hS104 _ hok, hS112 _ hok, hS120 _ hok, hS128 _ hok, hS136 _ hok, hS144 _ hok, hS152 _ hok, hS160 _ hok, hS168 _ hok] at e532a e532b ⊢
  subst v532a v532b
  refine r_add_lsr ne31_10 ne31_16 ne31_10 hrun hW hok (f06_536 hCL) (fun v536 e536 => ?_)
  simp only [regL_get_10, regL_get_16, regL_set_10, regL_set_16, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot] at e536 ⊢
  subst v536
  refine r_add_lsr ne31_11 ne31_18 ne31_11 hrun hW hok (f06_540 hCL) (fun v540 e540 => ?_)
  simp only [regL_get_11, regL_get_18, regL_set_11, regL_set_18, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot] at e540 ⊢
  subst v540
  refine r_movx ne31_5 ne31_22 hrun hW hok (f06_544 hCL) ?_
  simp only [regL_get_5, regL_get_22, regL_set_5, regL_set_22, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_eor ne31_16 ne31_0 ne31_22 hrun hW hok (f06_548 hCL) ?_
  simp only [regL_get_0, regL_get_16, regL_get_22, regL_set_0, regL_set_16, regL_set_22, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_ldr_sp ne31_22 hsp hrun hW hok (f06_552 hCL) (canRead_of hok (hR1 _ (by decide))) (fun v552 e552 => ?_)
  simp only [regL_get_22, regL_set_22, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, far_add_left_iff, far_add_right_iff, hS8 _ hok, hS24 _ hok, hS32 _ hok, hS40 _ hok, hS48 _ hok, hS56 _ hok, hS64 _ hok, hS72 _ hok, hS80 _ hok, hS88 _ hok, hS96 _ hok, hS104 _ hok, hS112 _ hok, hS120 _ hok, hS128 _ hok, hS136 _ hok, hS144 _ hok, hS152 _ hok, hS160 _ hok, hS168 _ hok] at e552 ⊢
  subst v552
  refine r_eor ne31_18 ne31_15 ne31_21 hrun hW hok (f06_556 hCL) ?_
  simp only [regL_get_15, regL_get_18, regL_get_21, regL_set_15, regL_set_18, regL_set_21, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_ldur_g ne31_21 ne31_29 hrun hW hok (f06_560 hCL) (canRead_of hok (hR2 _ _ (by decide))) (fun v560 e560 => ?_)
  simp only [regL_get_21, regL_get_29, regL_set_21, regL_set_29, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, far_add_left_iff, far_add_right_iff, hS8 _ hok, hS24 _ hok, hS32 _ hok, hS40 _ hok, hS48 _ hok, hS56 _ hok, hS64 _ hok, hS72 _ hok, hS80 _ hok, hS88 _ hok, hS96 _ hok, hS104 _ hok, hS112 _ hok, hS120 _ hok, hS128 _ hok, hS136 _ hok, hS144 _ hok, hS152 _ hok, hS160 _ hok, hS168 _ hok] at e560 ⊢
  subst v560
  refine r_ldur_g ne31_7 ne31_29 hrun hW hok (f06_564 hCL) (canRead_of hok (hR2 _ _ (by decide))) (fun v564 e564 => ?_)
  simp only [regL_get_7, regL_get_29, regL_set_7, regL_set_29, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, far_add_left_iff, far_add_right_iff, hS8 _ hok, hS24 _ hok, hS32 _ hok, hS40 _ hok, hS48 _ hok, hS56 _ hok, hS64 _ hok, hS72 _ hok, hS80 _ hok, hS88 _ hok, hS96 _ hok, hS104 _ hok, hS112 _ hok, hS120 _ hok, hS128 _ hok, hS136 _ hok, hS144 _ hok, hS152 _ hok, hS160 _ hok, hS168 _ hok] at e564 ⊢
  subst v564
  refine r_and ne31_16 ne31_16 ne31_9 hrun hW hok (f06_568 hCL) ?_
  simp only [regL_get_9, regL_get_16, regL_set_9, regL_set_16, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_ldr_sp ne31_4 hsp hrun hW hok (f06_572 hCL) (canRead_of hok (hR1 _ (by decide))) (fun v572 e572 => ?_)
  simp only [regL_get_4, regL_set_4, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, far_add_left_iff, far_add_right_iff, hS8 _ hok, hS24 _ hok, hS32 _ hok, hS40 _ hok, hS48 _ hok, hS56 _ hok, hS64 _ hok, hS72 _ hok, hS80 _ hok, hS88 _ hok, hS96 _ hok, hS104 _ hok, hS112 _ hok, hS120 _ hok, hS128 _ hok, hS136 _ hok, hS144 _ hok, hS152 _ hok, hS160 _ hok, hS168 _ hok] at e572 ⊢
  subst v572
  refine r_eor ne31_17 ne31_1 ne31_22 hrun hW hok (f06_576 hCL) ?_
  simp only [regL_get_1, regL_get_17, regL_get_22, regL_set_1, regL_set_17, regL_set_22, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_eor ne31_0 ne31_16 ne31_0 hrun hW hok (f06_580 hCL) ?_
  simp only [regL_get_0, regL_get_16, regL_set_0, regL_set_16, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_eor ne31_2 ne31_6 ne31_23 hrun hW hok (f06_584 hCL) ?_
  simp only [regL_get_2, regL_get_6, regL_get_23, regL_set_2, regL_set_6, regL_set_23, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_eor ne31_3 ne31_7 ne31_21 hrun hW hok (f06_588 hCL) ?_
  simp only [regL_get_3, regL_get_7, regL_get_21, regL_set_3, regL_set_7, regL_set_21, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_and ne31_17 ne31_17 ne31_9 hrun hW hok (f06_592 hCL) ?_
  simp only [regL_get_9, regL_get_17, regL_set_9, regL_set_17, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  exact h

theorem epiB_run {mpl : MultiPlacement} {P : State → Prop} {s : State} {S : BitVec 64}
    {m0 m : Memory} {ps : PState} {W : BitVec 64 → Prop}
    (hCL : (prog mpl 6).CodeLoaded m0) (hrun : s.status = .Running) (hW : WOwned m0 W)
    (hok : MemOK m0 W m) (hsp : S.toNat % 16 = 0)
    (hR1 : ∀ c : BitVec 64, c.toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c) 8)
    (hR2 : ∀ c1 c2 : BitVec 64, (c1 + c2).toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c1 + c2) 8)
    (hR3 : ∀ c1 c2 c3 : BitVec 64, (c1 + c2 + c3).toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c1 + c2 + c3) 8)
    {o : BitVec 64} {sv : BitVec 5 → BitVec 64}
    (hout : ∀ c : BitVec 64, c.toNat + 8 ≤ 120 → AllB W (o + c) 8)
    (hout2 : ∀ c1 c2 : BitVec 64, (c1 + c2).toNat + 8 ≤ 120 → AllB W (o + c1 + c2) 8) {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : BitVec 64}
    {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q25 q26 q30 q31 : BitVec 64} {c : Bool}
    (hS8 : ∀ m', MemOK m0 W m' → m'.read64 (S + 8#64) = o)
    (hS24 : ∀ m', MemOK m0 W m' → m'.read64 (S + 24#64) = a2)
    (hS32 : ∀ m', MemOK m0 W m' → m'.read64 (S + 32#64) = a1)
    (hS40 : ∀ m', MemOK m0 W m' → m'.read64 (S + 40#64) = a7)
    (hS48 : ∀ m', MemOK m0 W m' → m'.read64 (S + 48#64) = a4)
    (hS56 : ∀ m', MemOK m0 W m' → m'.read64 (S + 56#64) = a3)
    (hS64 : ∀ m', MemOK m0 W m' → m'.read64 (S + 64#64) = a8)
    (hS72 : ∀ m', MemOK m0 W m' → m'.read64 (S + 72#64) = a9)
    (hS80 : ∀ m', MemOK m0 W m' → m'.read64 (S + 80#64) = sv 29#5)
    (hS88 : ∀ m', MemOK m0 W m' → m'.read64 (S + 88#64) = sv 30#5)
    (hS96 : ∀ m', MemOK m0 W m' → m'.read64 (S + 96#64) = sv 28#5)
    (hS104 : ∀ m', MemOK m0 W m' → m'.read64 (S + 104#64) = sv 27#5)
    (hS112 : ∀ m', MemOK m0 W m' → m'.read64 (S + 112#64) = sv 26#5)
    (hS120 : ∀ m', MemOK m0 W m' → m'.read64 (S + 120#64) = sv 25#5)
    (hS128 : ∀ m', MemOK m0 W m' → m'.read64 (S + 128#64) = sv 24#5)
    (hS136 : ∀ m', MemOK m0 W m' → m'.read64 (S + 136#64) = sv 23#5)
    (hS144 : ∀ m', MemOK m0 W m' → m'.read64 (S + 144#64) = sv 22#5)
    (hS152 : ∀ m', MemOK m0 W m' → m'.read64 (S + 152#64) = sv 21#5)
    (hS160 : ∀ m', MemOK m0 W m' → m'.read64 (S + 160#64) = sv 20#5)
    (hS168 : ∀ m', MemOK m0 W m' → m'.read64 (S + 168#64) = sv 19#5)
    (hq0 : q0 &&& 255#64 = if c = true then 1#64 else 0#64)
    (h : ∀ (m' : Memory) (r' : BitVec 5 → BitVec 64), MemOK m0 W m' →
      m'.read64 o = (if c = true then a5 else a0) →
      m'.read64 (o + 8#64) = (if c = true then a6 else a1) →
      m'.read64 (o + 16#64) = (if c = true then a7 else a2) →
      m'.read64 (o + 24#64) = (if c = true then a8 else a3) →
      m'.read64 (o + 32#64) = (if c = true then a9 else a4) →
      m'.read64 (o + 40#64) = (if c = true then a0 else a5) →
      m'.read64 (o + 48#64) = (if c = true then a1 else a6) →
      m'.read64 (o + 56#64) = (if c = true then a2 else a7) →
      m'.read64 (o + 64#64) = (if c = true then a3 else a8) →
      m'.read64 (o + 72#64) = (if c = true then a4 else a9) →
      m'.read64 (o + 80#64) = (if c = true then nd0 a10 a14 else a10) →
      m'.read64 (o + 88#64) = (if c = true then nd1 a11 a10 else a11) →
      m'.read64 (o + 96#64) = (if c = true then ndk a12 a11 else a12) →
      m'.read64 (o + 104#64) = (if c = true then ndk a13 a12 else a13) →
      m'.read64 (o + 112#64) = (if c = true then ndk a14 a13 else a14) →
      r' 19#5 = sv 19#5 → r' 20#5 = sv 20#5 → r' 21#5 = sv 21#5 → r' 22#5 = sv 22#5 → r' 23#5 = sv 23#5 → r' 24#5 = sv 24#5 → r' 25#5 = sv 25#5 → r' 26#5 = sv 26#5 → r' 27#5 = sv 27#5 → r' 28#5 = sv 28#5 → r' 29#5 = sv 29#5 →
      P (mkS s (sv 30#5) r' (S + 176#64) m' ps)) :
    Reach mpl 6 P (mkS s (mpl.base 6 + BitVec.ofNat 64 596) (regL [if c = true then a6 else a1, a2, a3 ^^^ a8, a4 ^^^ a9, o, a6, a3, a4, (36028797018963952#64 - a14 &&& 2251799813685247#64) + (36028797018963952#64 - a13) >>> 51, if c = true then 18446744073709551615#64 else 0#64, (36028797018963952#64 - a12 &&& 2251799813685247#64) + (36028797018963952#64 - a11) >>> 51, (36028797018963952#64 - a13 &&& 2251799813685247#64) + (36028797018963952#64 - a12) >>> 51, (36028797018963952#64 - a11 &&& 2251799813685247#64) + (36028797018963664#64 - a10) >>> 51, (36028797018963664#64 - a10 &&& 2251799813685247#64) + BitVec.zeroExtend 64 (BitVec.truncate 32 ((36028797018963952#64 - a14) >>> 51)) * 19#64, if c = true then 1#64 else 0#64, if c = true then a0 ^^^ a5 else 0#64, if c = true then a1 ^^^ a6 else 0#64, if c = true then a2 ^^^ a7 else 0#64, if c = true then a5 else a0, a12, a11, a9, a7, a8, a10, a5, q26, a14, a13, S + 80#64, q30, q31]) S m ps) := by
  refine r_stp_g ne31_18 ne31_0 ne31_4 hrun hW hok (f06_596 hCL) (hout _ (by decide)) (hout2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_0, regL_get_4, regL_get_18, regL_set_0, regL_set_4, regL_set_18, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c] at hok ⊢
  refine r_and ne31_18 ne31_2 ne31_9 hrun hW hok (f06_600 hCL) ?_
  simp only [regL_get_2, regL_get_9, regL_get_18, regL_set_2, regL_set_9, regL_set_18, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_and ne31_2 ne31_3 ne31_9 hrun hW hok (f06_604 hCL) ?_
  simp only [regL_get_2, regL_get_3, regL_get_9, regL_set_2, regL_set_3, regL_set_9, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_eor ne31_1 ne31_17 ne31_1 hrun hW hok (f06_608 hCL) ?_
  simp only [regL_get_1, regL_get_17, regL_set_1, regL_set_17, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_eor ne31_3 ne31_2 ne31_7 hrun hW hok (f06_612 hCL) ?_
  simp only [regL_get_2, regL_get_3, regL_get_7, regL_set_2, regL_set_3, regL_set_7, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_eor ne31_15 ne31_15 ne31_25 hrun hW hok (f06_616 hCL) ?_
  simp only [regL_get_15, regL_get_25, regL_set_15, regL_set_25, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_eor ne31_16 ne31_16 ne31_5 hrun hW hok (f06_620 hCL) ?_
  simp only [regL_get_5, regL_get_16, regL_set_5, regL_set_16, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_eor ne31_17 ne31_17 ne31_22 hrun hW hok (f06_624 hCL) ?_
  simp only [regL_get_17, regL_get_22, regL_set_17, regL_set_22, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_subi ne31_14 ne31_14 hrun hW hok (f06_628 hCL) ?_
  simp only [regL_get_14, regL_set_14, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_stp_g ne31_3 ne31_15 ne31_4 hrun hW hok (f06_632 hCL) (hout _ (by decide)) (hout2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_3, regL_get_4, regL_get_15, regL_set_3, regL_set_4, regL_set_15, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c] at hok ⊢
  refine r_and ne31_13 ne31_13 ne31_9 hrun hW hok (f06_636 hCL) ?_
  simp only [regL_get_9, regL_get_13, regL_set_9, regL_set_13, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_and ne31_15 ne31_24 ne31_14 hrun hW hok (f06_640 hCL) ?_
  simp only [regL_get_14, regL_get_15, regL_get_24, regL_set_14, regL_set_15, regL_set_24, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_stp_g ne31_16 ne31_17 ne31_4 hrun hW hok (f06_644 hCL) (hout _ (by decide)) (hout2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_4, regL_get_16, regL_get_17, regL_set_4, regL_set_16, regL_set_17, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c] at hok ⊢
  refine r_and ne31_12 ne31_12 ne31_9 hrun hW hok (f06_648 hCL) ?_
  simp only [regL_get_9, regL_get_12, regL_set_9, regL_set_12, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_and ne31_16 ne31_20 ne31_14 hrun hW hok (f06_652 hCL) ?_
  simp only [regL_get_14, regL_get_16, regL_get_20, regL_set_14, regL_set_16, regL_set_20, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_eor ne31_0 ne31_18 ne31_6 hrun hW hok (f06_656 hCL) ?_
  simp only [regL_get_0, regL_get_6, regL_get_18, regL_set_0, regL_set_6, regL_set_18, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_orr ne31_13 ne31_13 ne31_15 hrun hW hok (f06_660 hCL) ?_
  simp only [regL_get_13, regL_get_15, regL_set_13, regL_set_15, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_orr ne31_12 ne31_12 ne31_16 hrun hW hok (f06_664 hCL) ?_
  simp only [regL_get_12, regL_get_16, regL_set_12, regL_set_16, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_and ne31_10 ne31_10 ne31_9 hrun hW hok (f06_668 hCL) ?_
  simp only [regL_get_9, regL_get_10, regL_set_9, regL_set_10, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_and ne31_15 ne31_19 ne31_14 hrun hW hok (f06_672 hCL) ?_
  simp only [regL_get_14, regL_get_15, regL_get_19, regL_set_14, regL_set_15, regL_set_19, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_and ne31_11 ne31_11 ne31_9 hrun hW hok (f06_676 hCL) ?_
  simp only [regL_get_9, regL_get_11, regL_set_9, regL_set_11, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_and ne31_16 ne31_28 ne31_14 hrun hW hok (f06_680 hCL) ?_
  simp only [regL_get_14, regL_get_16, regL_get_28, regL_set_14, regL_set_16, regL_set_28, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_and ne31_8 ne31_8 ne31_9 hrun hW hok (f06_684 hCL) ?_
  simp only [regL_get_8, regL_get_9, regL_set_8, regL_set_9, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_and ne31_9 ne31_27 ne31_14 hrun hW hok (f06_688 hCL) ?_
  simp only [regL_get_9, regL_get_14, regL_get_27, regL_set_9, regL_set_14, regL_set_27, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_stp_g ne31_1 ne31_0 ne31_4 hrun hW hok (f06_692 hCL) (hout _ (by decide)) (hout2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_0, regL_get_1, regL_get_4, regL_set_0, regL_set_1, regL_set_4, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c] at hok ⊢
  refine r_eor ne31_18 ne31_18 ne31_23 hrun hW hok (f06_696 hCL) ?_
  simp only [regL_get_18, regL_get_23, regL_set_18, regL_set_23, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_eor ne31_0 ne31_2 ne31_21 hrun hW hok (f06_700 hCL) ?_
  simp only [regL_get_0, regL_get_2, regL_get_21, regL_set_0, regL_set_2, regL_set_21, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_orr ne31_10 ne31_10 ne31_15 hrun hW hok (f06_704 hCL) ?_
  simp only [regL_get_10, regL_get_15, regL_set_10, regL_set_15, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_orr ne31_11 ne31_11 ne31_16 hrun hW hok (f06_708 hCL) ?_
  simp only [regL_get_11, regL_get_16, regL_set_11, regL_set_16, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_orr ne31_8 ne31_8 ne31_9 hrun hW hok (f06_712 hCL) ?_
  simp only [regL_get_8, regL_get_9, regL_set_8, regL_set_9, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c]
  refine r_stp_g ne31_18 ne31_0 ne31_4 hrun hW hok (f06_716 hCL) (hout _ (by decide)) (hout2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_0, regL_get_4, regL_get_18, regL_set_0, regL_set_4, regL_set_18, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c] at hok ⊢
  refine r_stp_g ne31_13 ne31_12 ne31_4 hrun hW hok (f06_720 hCL) (hout _ (by decide)) (hout2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_4, regL_get_12, regL_get_13, regL_set_4, regL_set_12, regL_set_13, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c] at hok ⊢
  refine r_stp_g ne31_10 ne31_11 ne31_4 hrun hW hok (f06_724 hCL) (hout _ (by decide)) (hout2 _ _ (by decide)) (fun hok => ?_)
  simp only [regL_get_4, regL_get_10, regL_get_11, regL_set_4, regL_set_10, regL_set_11, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c] at hok ⊢
  refine r_str_g ne31_8 ne31_4 hrun hW hok (f06_728 hCL) (hout _ (by decide)) (fun hok => ?_)
  simp only [regL_get_4, regL_get_8, regL_set_4, regL_set_8, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c] at hok ⊢
  refine r_ldp_sp ne31_20 ne31_19 hsp hrun hW hok (f06_732 hCL) (canRead_of hok (hR1 _ (by decide))) (canRead_of hok (hR2 _ _ (by decide))) (fun v732a v732b e732a e732b => ?_)
  simp only [regL_get_19, regL_get_20, regL_set_19, regL_set_20, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, far_add_left_iff, far_add_right_iff, hS8 _ hok, hS24 _ hok, hS32 _ hok, hS40 _ hok, hS48 _ hok, hS56 _ hok, hS64 _ hok, hS72 _ hok, hS80 _ hok, hS88 _ hok, hS96 _ hok, hS104 _ hok, hS112 _ hok, hS120 _ hok, hS128 _ hok, hS136 _ hok, hS144 _ hok, hS152 _ hok, hS160 _ hok, hS168 _ hok] at e732a e732b ⊢
  subst v732a v732b
  refine r_ldp_sp ne31_22 ne31_21 hsp hrun hW hok (f06_736 hCL) (canRead_of hok (hR1 _ (by decide))) (canRead_of hok (hR2 _ _ (by decide))) (fun v736a v736b e736a e736b => ?_)
  simp only [regL_get_21, regL_get_22, regL_set_21, regL_set_22, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, far_add_left_iff, far_add_right_iff, hS8 _ hok, hS24 _ hok, hS32 _ hok, hS40 _ hok, hS48 _ hok, hS56 _ hok, hS64 _ hok, hS72 _ hok, hS80 _ hok, hS88 _ hok, hS96 _ hok, hS104 _ hok, hS112 _ hok, hS120 _ hok, hS128 _ hok, hS136 _ hok, hS144 _ hok, hS152 _ hok, hS160 _ hok, hS168 _ hok] at e736a e736b ⊢
  subst v736a v736b
  refine r_ldp_sp ne31_24 ne31_23 hsp hrun hW hok (f06_740 hCL) (canRead_of hok (hR1 _ (by decide))) (canRead_of hok (hR2 _ _ (by decide))) (fun v740a v740b e740a e740b => ?_)
  simp only [regL_get_23, regL_get_24, regL_set_23, regL_set_24, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, far_add_left_iff, far_add_right_iff, hS8 _ hok, hS24 _ hok, hS32 _ hok, hS40 _ hok, hS48 _ hok, hS56 _ hok, hS64 _ hok, hS72 _ hok, hS80 _ hok, hS88 _ hok, hS96 _ hok, hS104 _ hok, hS112 _ hok, hS120 _ hok, hS128 _ hok, hS136 _ hok, hS144 _ hok, hS152 _ hok, hS160 _ hok, hS168 _ hok] at e740a e740b ⊢
  subst v740a v740b
  refine r_ldp_sp ne31_26 ne31_25 hsp hrun hW hok (f06_744 hCL) (canRead_of hok (hR1 _ (by decide))) (canRead_of hok (hR2 _ _ (by decide))) (fun v744a v744b e744a e744b => ?_)
  simp only [regL_get_25, regL_get_26, regL_set_25, regL_set_26, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, far_add_left_iff, far_add_right_iff, hS8 _ hok, hS24 _ hok, hS32 _ hok, hS40 _ hok, hS48 _ hok, hS56 _ hok, hS64 _ hok, hS72 _ hok, hS80 _ hok, hS88 _ hok, hS96 _ hok, hS104 _ hok, hS112 _ hok, hS120 _ hok, hS128 _ hok, hS136 _ hok, hS144 _ hok, hS152 _ hok, hS160 _ hok, hS168 _ hok] at e744a e744b ⊢
  subst v744a v744b
  refine r_ldp_sp ne31_28 ne31_27 hsp hrun hW hok (f06_748 hCL) (canRead_of hok (hR1 _ (by decide))) (canRead_of hok (hR2 _ _ (by decide))) (fun v748a v748b e748a e748b => ?_)
  simp only [regL_get_27, regL_get_28, regL_set_27, regL_set_28, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, far_add_left_iff, far_add_right_iff, hS8 _ hok, hS24 _ hok, hS32 _ hok, hS40 _ hok, hS48 _ hok, hS56 _ hok, hS64 _ hok, hS72 _ hok, hS80 _ hok, hS88 _ hok, hS96 _ hok, hS104 _ hok, hS112 _ hok, hS120 _ hok, hS128 _ hok, hS136 _ hok, hS144 _ hok, hS152 _ hok, hS160 _ hok, hS168 _ hok] at e748a e748b ⊢
  subst v748a v748b
  refine r_ldp_sp ne31_29 ne31_30 hsp hrun hW hok (f06_752 hCL) (canRead_of hok (hR1 _ (by decide))) (canRead_of hok (hR2 _ _ (by decide))) (fun v752a v752b e752a e752b => ?_)
  simp only [regL_get_29, regL_get_30, regL_set_29, regL_set_30, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot, hq0, neg_ite, sub1_ite, and_m1, and_m2, or_m, xor_sel1, xor_sel2, bf_lsr51, tr19, movk_c, read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, far_add_left_iff, far_add_right_iff, hS8 _ hok, hS24 _ hok, hS32 _ hok, hS40 _ hok, hS48 _ hok, hS56 _ hok, hS64 _ hok, hS72 _ hok, hS80 _ hok, hS88 _ hok, hS96 _ hok, hS104 _ hok, hS112 _ hok, hS120 _ hok, hS128 _ hok, hS136 _ hok, hS144 _ hok, hS152 _ hok, hS160 _ hok, hS168 _ hok] at e752a e752b ⊢
  subst v752a v752b
  refine r_addsp hrun hW hok (f06_756 hCL) ?_
  simp only [Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine r_ret hrun hW hok (f06_760 hCL) ?_
  simp only [regL_get_30, regL_set_30, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceNot]
  refine h _ _ hok ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  all_goals simp only [read64_write64_far, read64_write64_same, far_add_iff, read64_write32_far, read32_write64_far, read32_write32_far, read32_write32_same, farN_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, far_add_left_iff, far_add_right_iff, nd0, nd1, ndk]

theorem epi_run {mpl : MultiPlacement} {P : State → Prop} {s : State} {S : BitVec 64}
    {m0 m : Memory} {ps : PState} {W : BitVec 64 → Prop}
    (hCL : (prog mpl 6).CodeLoaded m0) (hrun : s.status = .Running) (hW : WOwned m0 W)
    (hok : MemOK m0 W m) (hsp : S.toNat % 16 = 0)
    (hR1 : ∀ c : BitVec 64, c.toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c) 8)
    (hR2 : ∀ c1 c2 : BitVec 64, (c1 + c2).toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c1 + c2) 8)
    (hR3 : ∀ c1 c2 c3 : BitVec 64, (c1 + c2 + c3).toNat + 8 ≤ 176 →
      AllB (fun x => (m0.perm x).r = true ∧ m0.isLazyFree x = false) (S + c1 + c2 + c3) 8)
    {o : BitVec 64} {sv : BitVec 5 → BitVec 64}
    (hout : ∀ c : BitVec 64, c.toNat + 8 ≤ 120 → AllB W (o + c) 8)
    (hout2 : ∀ c1 c2 : BitVec 64, (c1 + c2).toNat + 8 ≤ 120 → AllB W (o + c1 + c2) 8) {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : BitVec 64}
    {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q25 q26 q30 q31 : BitVec 64} {c : Bool}
    (hS8 : ∀ m', MemOK m0 W m' → m'.read64 (S + 8#64) = o)
    (hS24 : ∀ m', MemOK m0 W m' → m'.read64 (S + 24#64) = a2)
    (hS32 : ∀ m', MemOK m0 W m' → m'.read64 (S + 32#64) = a1)
    (hS40 : ∀ m', MemOK m0 W m' → m'.read64 (S + 40#64) = a7)
    (hS48 : ∀ m', MemOK m0 W m' → m'.read64 (S + 48#64) = a4)
    (hS56 : ∀ m', MemOK m0 W m' → m'.read64 (S + 56#64) = a3)
    (hS64 : ∀ m', MemOK m0 W m' → m'.read64 (S + 64#64) = a8)
    (hS72 : ∀ m', MemOK m0 W m' → m'.read64 (S + 72#64) = a9)
    (hS80 : ∀ m', MemOK m0 W m' → m'.read64 (S + 80#64) = sv 29#5)
    (hS88 : ∀ m', MemOK m0 W m' → m'.read64 (S + 88#64) = sv 30#5)
    (hS96 : ∀ m', MemOK m0 W m' → m'.read64 (S + 96#64) = sv 28#5)
    (hS104 : ∀ m', MemOK m0 W m' → m'.read64 (S + 104#64) = sv 27#5)
    (hS112 : ∀ m', MemOK m0 W m' → m'.read64 (S + 112#64) = sv 26#5)
    (hS120 : ∀ m', MemOK m0 W m' → m'.read64 (S + 120#64) = sv 25#5)
    (hS128 : ∀ m', MemOK m0 W m' → m'.read64 (S + 128#64) = sv 24#5)
    (hS136 : ∀ m', MemOK m0 W m' → m'.read64 (S + 136#64) = sv 23#5)
    (hS144 : ∀ m', MemOK m0 W m' → m'.read64 (S + 144#64) = sv 22#5)
    (hS152 : ∀ m', MemOK m0 W m' → m'.read64 (S + 152#64) = sv 21#5)
    (hS160 : ∀ m', MemOK m0 W m' → m'.read64 (S + 160#64) = sv 20#5)
    (hS168 : ∀ m', MemOK m0 W m' → m'.read64 (S + 168#64) = sv 19#5)
    (hq0 : q0 &&& 255#64 = if c = true then 1#64 else 0#64)
    (h : ∀ (m' : Memory) (r' : BitVec 5 → BitVec 64), MemOK m0 W m' →
      m'.read64 o = (if c = true then a5 else a0) →
      m'.read64 (o + 8#64) = (if c = true then a6 else a1) →
      m'.read64 (o + 16#64) = (if c = true then a7 else a2) →
      m'.read64 (o + 24#64) = (if c = true then a8 else a3) →
      m'.read64 (o + 32#64) = (if c = true then a9 else a4) →
      m'.read64 (o + 40#64) = (if c = true then a0 else a5) →
      m'.read64 (o + 48#64) = (if c = true then a1 else a6) →
      m'.read64 (o + 56#64) = (if c = true then a2 else a7) →
      m'.read64 (o + 64#64) = (if c = true then a3 else a8) →
      m'.read64 (o + 72#64) = (if c = true then a4 else a9) →
      m'.read64 (o + 80#64) = (if c = true then nd0 a10 a14 else a10) →
      m'.read64 (o + 88#64) = (if c = true then nd1 a11 a10 else a11) →
      m'.read64 (o + 96#64) = (if c = true then ndk a12 a11 else a12) →
      m'.read64 (o + 104#64) = (if c = true then ndk a13 a12 else a13) →
      m'.read64 (o + 112#64) = (if c = true then ndk a14 a13 else a14) →
      r' 19#5 = sv 19#5 → r' 20#5 = sv 20#5 → r' 21#5 = sv 21#5 → r' 22#5 = sv 22#5 → r' 23#5 = sv 23#5 → r' 24#5 = sv 24#5 → r' 25#5 = sv 25#5 → r' 26#5 = sv 26#5 → r' 27#5 = sv 27#5 → r' 28#5 = sv 28#5 → r' 29#5 = sv 29#5 →
      P (mkS s (sv 30#5) r' (S + 176#64) m' ps)) :
    Reach mpl 6 P (mkS s (mpl.base 6 + BitVec.ofNat 64 436) (regL [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, a12, a11, a0, a6, a5, a10, q25, q26, a14, a13, S + 80#64, q30, q31]) S m ps) :=
  epiA_run hCL hrun hW hok hsp hR1 hR2 hR3 hout hout2 hS8 hS24 hS32 hS40 hS48 hS56 hS64 hS72 hS80 hS88 hS96 hS104 hS112 hS120 hS128 hS136 hS144 hS152 hS160 hS168 hq0
    (epiB_run (q1 := q1) (q2 := q2) (q3 := q3) (q4 := q4) (q5 := q5) (q6 := q6) (q7 := q7) (q8 := q8)
      (q9 := q9) (q10 := q10) (q11 := q11) (q12 := q12) (q13 := q13) (q14 := q14) (q15 := q15)
      (q16 := q16) (q17 := q17) (q18 := q18) (q25 := q25)
      hCL hrun hW hok hsp hR1 hR2 hR3 hout hout2 hS8 hS24 hS32 hS40 hS48 hS56 hS64 hS72 hS80 hS88 hS96 hS104 hS112 hS120 hS128 hS136 hS144 hS152 hS160 hS168 hq0 h)

end X25519Dalek.ESel
end

section
/-! # The memory invariant of block 6 between calls

`MI m`: the 16-byte callee frame below `S`, the 176-byte frame `[S, S + 176)` and the 120-byte
output, each holding the current bytes of `m`, the read-only table, and the caller's frame `R`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.ESel

open Arm64 Arm64.Obj

def MI (m : Memory) (S O T : BitVec 64) (tb : List (BitVec 8)) (R : SepProp) : Prop :=
  m ⊨ (memRegion (S - 16#64) 16 ∗ ((S ↦ₛ bytesAt m S 176) ∗ ((O ↦ₛ bytesAt m O 120) ∗ (T ↦ᵣ tb)))) ∗ R

theorem ownsRW_mono {P : SepProp} {W W' : BitVec 64 → Prop} (h : OwnsRW P W) (hw : ∀ a, W' a → W a) :
    OwnsRW P W' := fun h1 hp a ha => h h1 hp a (hw a ha)

theorem mi_owns (m : Memory) (S O T : BitVec 64) (tb : List (BitVec 8)) :
    OwnsRW (memRegion (S - 16#64) 16 ∗ ((S ↦ₛ bytesAt m S 176) ∗ ((O ↦ₛ bytesAt m O 120) ∗ (T ↦ᵣ tb))))
      (fun a => InRegion S 176 a ∨ InRegion O 120 a) := by
  have h1 := ownsRW_bytes (bytesAt m S 176) S
  have h2 := ownsRW_bytes (bytesAt m O 120) O
  rw [bytesAt_length] at h1 h2
  exact ownsRW_sep_right (ownsRW_or (ownsRW_sep_left h1) (ownsRW_sep_right (ownsRW_sep_left h2)))

theorem mi_wowned {m : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hmi : MI m S O T tb R) {W : BitVec 64 → Prop}
    (hw : ∀ a, W a → InRegion S 176 a ∨ InRegion O 120 a) : WOwned m W :=
  wowned_of hmi (ownsRW_mono (mi_owns m S O T tb) hw)

theorem mi_frame {m0 m : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hmi : MI m0 S O T tb R) {W : BitVec 64 → Prop} (hok : MemOK m0 W m)
    (hw : ∀ a, W a → InRegion S 176 a ∨ InRegion O 120 a) : MI m S O T tb R := by
  have hrf := rf_sep (rf_region m (S - 16#64) 16) (rf_sep (rf_bytes m (bytesAt m0 S 176) S)
    (rf_sep (rf_bytes m (bytesAt m0 O 120) O) (rf_ro m tb T)))
  rw [bytesAt_length, bytesAt_length] at hrf
  exact frame hmi hok (ownsRW_mono (mi_owns m0 S O T tb) hw) hrf

/-! ## Cells -/

theorem sat_rw_cell {m : Memory} {P R : SepProp} {x : BitVec 64} {b : BitVec 8}
    (hs : m ⊨ P ∗ R) (hc : ∀ h, P.holds h → h.phys x = some (.rw b)) :
    m.read8 x = b ∧ m.perm x = some Perm.rw ∧ m.isLazyFree x = false := by
  obtain ⟨h, hh, hm⟩ := hs
  exact hm.1 _ _ (cell_sep_left hh hc)

theorem sat_ro_cell {m : Memory} {P R : SepProp} {x : BitVec 64} {b : BitVec 8}
    (hs : m ⊨ P ∗ R) (hc : ∀ h, P.holds h → h.phys x = some (.ro b)) :
    m.read8 x = b ∧ (m.perm x).r = true ∧ m.isLazyFree x = false := by
  obtain ⟨h, hh, hm⟩ := hs
  exact hm.1 _ _ (cell_sep_left hh hc)

theorem mi_stk_cell (m : Memory) (S O T : BitVec 64) (tb : List (BitVec 8)) (i : Nat) (hi : i < 176) :
    ∀ h, (memRegion (S - 16#64) 16 ∗ ((S ↦ₛ bytesAt m S 176) ∗ ((O ↦ₛ bytesAt m O 120) ∗ (T ↦ᵣ tb)))).holds h →
      h.phys (S + BitVec.ofNat 64 i) = some (.rw ((bytesAt m S 176)[i]'(by rw [bytesAt_length]; exact hi))) :=
  fun _ p => cell_sep_right p fun _ p2 => cell_sep_left p2 fun h3 p3 =>
    rwCells_bytes _ S h3 p3 i (by rw [bytesAt_length]; exact hi)

theorem mi_out_cell (m : Memory) (S O T : BitVec 64) (tb : List (BitVec 8)) (i : Nat) (hi : i < 120) :
    ∀ h, (memRegion (S - 16#64) 16 ∗ ((S ↦ₛ bytesAt m S 176) ∗ ((O ↦ₛ bytesAt m O 120) ∗ (T ↦ᵣ tb)))).holds h →
      h.phys (O + BitVec.ofNat 64 i) = some (.rw ((bytesAt m O 120)[i]'(by rw [bytesAt_length]; exact hi))) :=
  fun _ p => cell_sep_right p fun _ p2 => cell_sep_right p2 fun _ p3 => cell_sep_left p3 fun h4 p4 =>
    rwCells_bytes _ O h4 p4 i (by rw [bytesAt_length]; exact hi)

theorem mi_tbl_cell (m : Memory) (S O T : BitVec 64) (tb : List (BitVec 8)) (i : Nat) (hi : i < tb.length) :
    ∀ h, (memRegion (S - 16#64) 16 ∗ ((S ↦ₛ bytesAt m S 176) ∗ ((O ↦ₛ bytesAt m O 120) ∗ (T ↦ᵣ tb)))).holds h →
      h.phys (T + BitVec.ofNat 64 i) = some (.ro tb[i]) :=
  fun _ p => cell_sep_right p fun _ p2 => cell_sep_right p2 fun _ p3 => cell_sep_right p3 fun h4 p4 =>
    roCells_bytes tb T h4 p4 i hi

theorem bytesAt_getElem (m : Memory) (a : BitVec 64) (n i : Nat) (hi : i < (bytesAt m a n).length) :
    (bytesAt m a n)[i] = m.read8 (a + BitVec.ofNat 64 i) := by
  simp [bytesAt]

/-- Stack bytes are readable. -/
theorem mi_rd {m : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hmi : MI m S O T tb R) (i : Nat) (hi : i < 176) :
    (m.perm (S + BitVec.ofNat 64 i)).r = true ∧ m.isLazyFree (S + BitVec.ofNat 64 i) = false := by
  have := sat_rw_cell hmi (mi_stk_cell m S O T tb i hi)
  rw [this.2.1]; exact ⟨rfl, this.2.2⟩

theorem addr_split (S c : BitVec 64) (j : Nat) (hj : j < 8) (hc : c.toNat + 8 ≤ 176) :
    S + c + BitVec.ofNat 64 j = S + BitVec.ofNat 64 (c.toNat + j) := by
  rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp <;> omega

theorem mi_rd1 {m : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hmi : MI m S O T tb R) : ∀ c : BitVec 64, c.toNat + 8 ≤ 176 →
      AllB (fun x => (m.perm x).r = true ∧ m.isLazyFree x = false) (S + c) 8 := by
  intro c hc j hj
  rw [addr_split S c j hj hc]
  exact mi_rd hmi _ (by omega)

theorem mi_rd2 {m : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hmi : MI m S O T tb R) : ∀ c1 c2 : BitVec 64, (c1 + c2).toNat + 8 ≤ 176 →
      AllB (fun x => (m.perm x).r = true ∧ m.isLazyFree x = false) (S + c1 + c2) 8 := by
  intro c1 c2 hc
  rw [BitVec.add_assoc]; exact mi_rd1 hmi _ hc

theorem mi_rd3 {m : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hmi : MI m S O T tb R) : ∀ c1 c2 c3 : BitVec 64, (c1 + c2 + c3).toNat + 8 ≤ 176 →
      AllB (fun x => (m.perm x).r = true ∧ m.isLazyFree x = false) (S + c1 + c2 + c3) 8 := by
  intro c1 c2 c3 hc
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.add_assoc c1]; exact mi_rd1 hmi _ hc

/-- Table bytes are in memory, readable, and outside the stack frame and the output. -/
theorem mi_tbl {m : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hmi : MI m S O T tb R) (i : Nat) (hi : i < tb.length) :
    m.read8 (T + BitVec.ofNat 64 i) = tb[i] ∧ (m.perm (T + BitVec.ofNat 64 i)).r = true ∧
      m.isLazyFree (T + BitVec.ofNat 64 i) = false ∧
      ¬ (InRegion S 176 (T + BitVec.ofNat 64 i) ∨ InRegion O 120 (T + BitVec.ofNat 64 i)) := by
  refine ⟨(sat_ro_cell hmi (mi_tbl_cell m S O T tb i hi)).1, (sat_ro_cell hmi (mi_tbl_cell m S O T tb i hi)).2.1,
    (sat_ro_cell hmi (mi_tbl_cell m S O T tb i hi)).2.2, ?_⟩
  obtain ⟨h, hh, -⟩ := hmi
  have ht := cell_sep_left hh (mi_tbl_cell m S O T tb i hi)
  rintro (hS | hO)
  · have e : T + BitVec.ofNat 64 i = S + BitVec.ofNat 64 ((T + BitVec.ofNat 64 i - S).toNat) := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; abel
    have hs := cell_sep_left hh (mi_stk_cell m S O T tb _ hS)
    rw [← e, ht] at hs; cases hs
  · have e : T + BitVec.ofNat 64 i = O + BitVec.ofNat 64 ((T + BitVec.ofNat 64 i - O).toNat) := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; abel
    have hs := cell_sep_left hh (mi_out_cell m S O T tb _ hO)
    rw [← e, ht] at hs; cases hs

/-! ## Across a call -/

theorem mi_call {m mf : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hf : mf ⊨ memRegion (S - 16#64) 16 ∗
      (((S ↦ₛ bytesAt m S 176) ∗ ((O ↦ₛ bytesAt m O 120) ∗ (T ↦ᵣ tb))) ∗ R)) :
    MI mf S O T tb R ∧ ∀ i, i < 176 → mf.read8 (S + BitVec.ofNat 64 i) = m.read8 (S + BitVec.ofNat 64 i) := by
  rw [← sepConj_assoc] at hf
  have hS : ∀ i, i < 176 → mf.read8 (S + BitVec.ofNat 64 i) = m.read8 (S + BitVec.ofNat 64 i) := by
    intro i hi
    have := (sat_rw_cell hf (fun _ p => cell_sep_right p fun _ p2 => cell_sep_left p2 fun h3 p3 =>
      rwCells_bytes _ S h3 p3 i (by rw [bytesAt_length]; exact hi))).1
    rw [this, bytesAt_getElem]
  have hO : ∀ i, i < 120 → mf.read8 (O + BitVec.ofNat 64 i) = m.read8 (O + BitVec.ofNat 64 i) := by
    intro i hi
    have := (sat_rw_cell hf (fun _ p => cell_sep_right p fun _ p2 => cell_sep_right p2 fun _ p3 =>
      cell_sep_left p3 fun h4 p4 => rwCells_bytes _ O h4 p4 i (by rw [bytesAt_length]; exact hi))).1
    rw [this, bytesAt_getElem]
  have eS : bytesAt mf S 176 = bytesAt m S 176 := by
    apply List.ext_getElem (by simp [bytesAt_length]); intro i h1 h2
    rw [bytesAt_getElem, bytesAt_getElem, hS i (by rw [bytesAt_length] at h1; exact h1)]
  have eO : bytesAt mf O 120 = bytesAt m O 120 := by
    apply List.ext_getElem (by simp [bytesAt_length]); intro i h1 h2
    rw [bytesAt_getElem, bytesAt_getElem, hO i (by rw [bytesAt_length] at h1; exact h1)]
  refine ⟨?_, hS⟩
  unfold MI; rw [eS, eO]; exact hf

theorem mi_pre_call {m : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hmi : MI m S O T tb R) :
    m ⊨ memRegion (S - 16#64) 16 ∗ (((S ↦ₛ bytesAt m S 176) ∗ ((O ↦ₛ bytesAt m O 120) ∗ (T ↦ᵣ tb))) ∗ R) := by
  unfold MI at hmi; rwa [sepConj_assoc] at hmi

/-! ## Words from bytes -/

theorem read64_of_bytes {m m' : Memory} {a : BitVec 64}
    (h : ∀ k, k < 8 → m'.read8 (a + BitVec.ofNat 64 k) = m.read8 (a + BitVec.ofNat 64 k)) :
    m'.read64 a = m.read64 a := by
  simp only [Memory.read64]
  rw [show a + 0#64 = a + BitVec.ofNat 64 0 from rfl, h 0 (by omega),
    show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, h 1 (by omega),
    show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, h 2 (by omega),
    show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, h 3 (by omega),
    show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, h 4 (by omega),
    show (5#64 : BitVec 64) = BitVec.ofNat 64 5 from rfl, h 5 (by omega),
    show (6#64 : BitVec 64) = BitVec.ofNat 64 6 from rfl, h 6 (by omega),
    show (7#64 : BitVec 64) = BitVec.ofNat 64 7 from rfl, h 7 (by omega)]

theorem read32_of_bytes {m m' : Memory} {a : BitVec 64}
    (h : ∀ k, k < 4 → m'.read8 (a + BitVec.ofNat 64 k) = m.read8 (a + BitVec.ofNat 64 k)) :
    m'.read32 a = m.read32 a := by
  simp only [Memory.read32]
  rw [show a + 0#64 = a + BitVec.ofNat 64 0 from rfl, h 0 (by omega),
    show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, h 1 (by omega),
    show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, h 2 (by omega),
    show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, h 3 (by omega)]

/-- Bytes of `[S, S + 176)` outside `[S + 24, S + 80)` agree. -/
def FixB (m m' : Memory) (S : BitVec 64) : Prop :=
  ∀ i, i < 176 → (i < 24 ∨ 80 ≤ i) → m'.read8 (S + BitVec.ofNat 64 i) = m.read8 (S + BitVec.ofNat 64 i)

theorem fixB_word {m m' : Memory} {S : BitVec 64} (h : FixB m m' S) (c n : Nat) (hn : n ≤ 8)
    (hc : c + n ≤ 176) (hcc : c + n ≤ 24 ∨ 80 ≤ c) :
    ∀ k, k < n → m'.read8 (S + BitVec.ofNat 64 c + BitVec.ofNat 64 k) =
      m.read8 (S + BitVec.ofNat 64 c + BitVec.ofNat 64 k) := by
  intro k hk
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega) (by omega)

theorem fx_of_fixB {m m' : Memory} {S X : BitVec 64} {sv : BitVec 5 → BitVec 64}
    (h : FixB m m' S) (hf : Fx m S X sv) : Fx m' S X sv := by
  obtain ⟨f4, f8, f16, f20, f80, f88, f96, f104, f112, f120, f128, f136, f144, f152, f160, f168⟩ := hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← f4]; exact read32_of_bytes (fixB_word h 4 4 (by omega) (by omega) (by omega))
  · rw [← f8]; exact read64_of_bytes (fixB_word h 8 8 (by omega) (by omega) (by omega))
  · rw [← f16]; exact read32_of_bytes (fixB_word h 16 4 (by omega) (by omega) (by omega))
  · rw [← f20]; exact read32_of_bytes (fixB_word h 20 4 (by omega) (by omega) (by omega))
  · rw [← f80]; exact read64_of_bytes (fixB_word h 80 8 (by omega) (by omega) (by omega))
  · rw [← f88]; exact read64_of_bytes (fixB_word h 88 8 (by omega) (by omega) (by omega))
  · rw [← f96]; exact read64_of_bytes (fixB_word h 96 8 (by omega) (by omega) (by omega))
  · rw [← f104]; exact read64_of_bytes (fixB_word h 104 8 (by omega) (by omega) (by omega))
  · rw [← f112]; exact read64_of_bytes (fixB_word h 112 8 (by omega) (by omega) (by omega))
  · rw [← f120]; exact read64_of_bytes (fixB_word h 120 8 (by omega) (by omega) (by omega))
  · rw [← f128]; exact read64_of_bytes (fixB_word h 128 8 (by omega) (by omega) (by omega))
  · rw [← f136]; exact read64_of_bytes (fixB_word h 136 8 (by omega) (by omega) (by omega))
  · rw [← f144]; exact read64_of_bytes (fixB_word h 144 8 (by omega) (by omega) (by omega))
  · rw [← f152]; exact read64_of_bytes (fixB_word h 152 8 (by omega) (by omega) (by omega))
  · rw [← f160]; exact read64_of_bytes (fixB_word h 160 8 (by omega) (by omega) (by omega))
  · rw [← f168]; exact read64_of_bytes (fixB_word h 168 8 (by omega) (by omega) (by omega))

theorem acc_of_all {m m' : Memory} {S a1 a2 a3 a4 a7 a8 a9 : BitVec 64}
    (h : ∀ i, i < 176 → m'.read8 (S + BitVec.ofNat 64 i) = m.read8 (S + BitVec.ofNat 64 i))
    (ha : Acc m S a1 a2 a3 a4 a7 a8 a9) : Acc m' S a1 a2 a3 a4 a7 a8 a9 := by
  have w : ∀ c, c + 8 ≤ 176 → m'.read64 (S + BitVec.ofNat 64 c) = m.read64 (S + BitVec.ofNat 64 c) :=
    fun c hc => read64_of_bytes fun k hk => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h _ (by omega)
  obtain ⟨b1, b2, b3, b4, b7, b8, b9⟩ := ha
  exact ⟨by rw [← b1]; exact w 32 (by omega), by rw [← b2]; exact w 24 (by omega),
    by rw [← b3]; exact w 56 (by omega), by rw [← b4]; exact w 48 (by omega),
    by rw [← b7]; exact w 40 (by omega), by rw [← b8]; exact w 64 (by omega),
    by rw [← b9]; exact w 72 (by omega)⟩

/-! ## Code stays loaded across stores to owned writable bytes -/

theorem cl_memOK {p : Program} {m0 m : Memory} {W : BitVec 64 → Prop} (hW : WOwned m0 W)
    (hok : MemOK m0 W m) (h : p.CodeLoaded m0) : p.CodeLoaded m := by
  unfold Program.CodeLoaded at h ⊢
  refine ⟨h.1, h.2.1, fun i hi => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.2.2 i hi
  obtain ⟨k1, k2, _, k4⟩ := hok (p.base + BitVec.ofNat 64 i)
  have nw : ¬ W (p.base + BitVec.ofNat 64 i) := fun hw => by
    rw [(hW _ hw).1] at h2; cases h2
  exact ⟨by rw [k4 nw, h1], by rw [k1, h2], by rw [k2, h3]⟩

theorem libcl_memOK {mpl : MultiPlacement} {m0 m : Memory} {W : BitVec 64 → Prop} (hW : WOwned m0 W)
    (hok : MemOK m0 W m) (h : x25519CliMultiLib.CodeLoaded mpl m0) : x25519CliMultiLib.CodeLoaded mpl m :=
  fun i hi => cl_memOK hW hok (h i hi)

end X25519Dalek.ESel
end

section
/-! # The selection, the conditional negation, and the postcondition

`fe51Reduce_bounded`, `fe51Reduce_val_mod` and `fe51Neg_val_mod` are copied from DeepMind's
`Shared51/SliceBase.lean` (google-deepmind/code-verification @ 8c8d371f, Apache-2.0); the
case analysis of `final_post` follows DeepMind's `writeSelectEpilogue_spec`
(`Shared51/BasepointTable1.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.ESel

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj

/-- `x = n` or `x = -n` (the test of the `n`-th iteration of the selection loop). -/
def selC (x : BitVec 8) (n : Nat) : Bool := x == BitVec.ofNat 8 n || x == -BitVec.ofNat 8 n

/-- Limb `k` of the selection after `j` iterations: the identity `(1, 1, 0)` replaced by the
`i`-th table entry when `x = ±(i+1)`. -/
def selAcc (tb : List (BitVec 8)) (x : BitVec 8) : Nat → Nat → BitVec 64
  | 0, k => if k = 0 ∨ k = 5 then 1#64 else 0#64
  | j + 1, k => if selC x (j + 1) = true then ByteSlice.readLE tb (120 * j + 8 * k) 8 else selAcc tb x j k

theorem selAcc_succ (tb : List (BitVec 8)) (x : BitVec 8) (j k : Nat) :
    selAcc tb x (j + 1) k = if selC x (j + 1) = true then ByteSlice.readLE tb (120 * j + 8 * k) 8
      else selAcc tb x j k := rfl

/-! ## The loop test -/

theorem signW_eq (X : BitVec 64) :
    signW X = if (X.truncate 8).getLsbD 7 = true then 0xffffffff#32 else 0#32 := by
  simp [signW]

theorem cz_sel (X : BitVec 64) (j : Nat) (hj : j < 8) :
    CZ (signW X + sxtbW X) (signW X) (BitVec.ofNat 64 (j + 1)) = selC (X.truncate 8) (j + 1) := by
  rw [signW_eq, sxtbW]
  generalize X.truncate 8 = x
  revert x
  interval_cases j <;> decide +kernel

theorem msb_eq (X : BitVec 64) : X.getLsbD 7 = (X.truncate 8).msb := by
  simp [BitVec.msb_eq_getLsbD_last]

/-! ## Limb bounds -/

theorem entry_lt {tb : List (BitVec 8)} {B base : Nat} (h : fe51AffineNielsBoundedAt tb base B) :
    ∀ k, k < 15 → (ByteSlice.readLE tb (base + 8 * k) 8).toNat < B := by
  obtain ⟨⟨a0, a1, a2, a3, a4⟩, ⟨b0, b1, b2, b3, b4⟩, ⟨c0, c1, c2, c3, c4⟩⟩ := h
  intro k hk
  interval_cases k
  · simpa using a0
  · rw [show base + 8 * 1 = base + 8 by omega]; exact a1
  · rw [show base + 8 * 2 = base + 16 by omega]; exact a2
  · rw [show base + 8 * 3 = base + 24 by omega]; exact a3
  · rw [show base + 8 * 4 = base + 32 by omega]; exact a4
  · rw [show base + 8 * 5 = base + 40 by omega]; exact b0
  · rw [show base + 8 * 6 = base + 40 + 8 by omega]; exact b1
  · rw [show base + 8 * 7 = base + 40 + 16 by omega]; exact b2
  · rw [show base + 8 * 8 = base + 40 + 24 by omega]; exact b3
  · rw [show base + 8 * 9 = base + 40 + 32 by omega]; exact b4
  · rw [show base + 8 * 10 = base + 80 by omega]; exact c0
  · rw [show base + 8 * 11 = base + 80 + 8 by omega]; exact c1
  · rw [show base + 8 * 12 = base + 80 + 16 by omega]; exact c2
  · rw [show base + 8 * 13 = base + 80 + 24 by omega]; exact c3
  · rw [show base + 8 * 14 = base + 80 + 32 by omega]; exact c4

theorem tbl_lt {tb : List (BitVec 8)} (htb : fe51LookupTable8Bounded tb (2 ^ 53)) :
    ∀ j, j < 8 → ∀ k, k < 15 → (ByteSlice.readLE tb (120 * j + 8 * k) 8).toNat < 2 ^ 53 := by
  obtain ⟨_, h0, h1, h2, h3, h4, h5, h6, h7⟩ := htb
  intro j hj k hk
  interval_cases j
  · simpa using entry_lt h0 k hk
  · exact entry_lt h1 k hk
  · exact entry_lt h2 k hk
  · exact entry_lt h3 k hk
  · exact entry_lt h4 k hk
  · exact entry_lt h5 k hk
  · exact entry_lt h6 k hk
  · exact entry_lt h7 k hk

theorem selAcc_lt {tb : List (BitVec 8)} (x : BitVec 8) (htb : fe51LookupTable8Bounded tb (2 ^ 53)) :
    ∀ j, j ≤ 8 → ∀ k, k < 15 → (selAcc tb x j k).toNat < 2 ^ 53 := by
  intro j
  induction j with
  | zero => intro _ k _; simp only [selAcc]; split <;> simp
  | succ j ih =>
    intro hj k hk
    rw [selAcc_succ]
    split
    · exact tbl_lt htb j (by omega) k hk
    · exact ih (by omega) k hk

/-! ## FieldElement51 negation (DeepMind, `SliceBase.lean`) -/

theorem mask51_toNat (d : BitVec 64) :
    (d &&& 2251799813685247#64).toNat = d.toNat % 2 ^ 51 := by
  rw [BitVec.toNat_and, show (2251799813685247#64).toNat = 2 ^ 51 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem lsr51_toNat (d : BitVec 64) :
    (d >>> 51).toNat = d.toNat / 2 ^ 51 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem umaddl19_lsr51_toNat (d0 d4 : BitVec 64) :
    ((d0 &&& 2251799813685247#64) +
      BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64).toNat =
      d0.toNat % 2 ^ 51 + (d4.toNat / 2 ^ 51) * 19 := by
  have hd4 : d4.toNat < 2 ^ 64 := d4.isLt
  have hze : (BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51))).toNat = d4.toNat / 2 ^ 51 := by
    simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, lsr51_toNat]
    omega
  have hm := mask51_toNat d0
  rw [BitVec.toNat_add, BitVec.toNat_mul, hze, hm, show (19#64).toNat = 19 from rfl]
  omega

theorem add_mask51_lsr51_toNat (di dprev : BitVec 64) :
    ((di &&& 2251799813685247#64) + (dprev >>> 51)).toNat =
      di.toNat % 2 ^ 51 + dprev.toNat / 2 ^ 51 := by
  have hprev : dprev.toNat < 2 ^ 64 := dprev.isLt
  rw [BitVec.toNat_add, mask51_toNat, lsr51_toNat]
  omega

theorem fe51Reduce_bounded (d0 d1 d2 d3 d4 : BitVec 64) :
    ((d0 &&& 2251799813685247#64) +
      BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64).toNat < 2 ^ 52 ∧
    ((d1 &&& 2251799813685247#64) + (d0 >>> 51)).toNat < 2 ^ 52 ∧
    ((d2 &&& 2251799813685247#64) + (d1 >>> 51)).toNat < 2 ^ 52 ∧
    ((d3 &&& 2251799813685247#64) + (d2 >>> 51)).toNat < 2 ^ 52 ∧
    ((d4 &&& 2251799813685247#64) + (d3 >>> 51)).toNat < 2 ^ 52 := by
  have h0 := d0.isLt; have h1 := d1.isLt; have h2 := d2.isLt; have h3 := d3.isLt; have h4 := d4.isLt
  rw [umaddl19_lsr51_toNat, add_mask51_lsr51_toNat, add_mask51_lsr51_toNat,
    add_mask51_lsr51_toNat, add_mask51_lsr51_toNat]
  omega

theorem fe51Reduce_val_mod (d0 d1 d2 d3 d4 : BitVec 64) :
    fe51Val
      ((d0 &&& 2251799813685247#64) +
        BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64)
      ((d1 &&& 2251799813685247#64) + (d0 >>> 51))
      ((d2 &&& 2251799813685247#64) + (d1 >>> 51))
      ((d3 &&& 2251799813685247#64) + (d2 >>> 51))
      ((d4 &&& 2251799813685247#64) + (d3 >>> 51)) % p25519 =
    fe51Val d0 d1 d2 d3 d4 % p25519 := by
  have hid :
      fe51Val
        ((d0 &&& 2251799813685247#64) +
          BitVec.zeroExtend 64 (BitVec.truncate 32 (d4 >>> 51)) * 19#64)
        ((d1 &&& 2251799813685247#64) + (d0 >>> 51))
        ((d2 &&& 2251799813685247#64) + (d1 >>> 51))
        ((d3 &&& 2251799813685247#64) + (d2 >>> 51))
        ((d4 &&& 2251799813685247#64) + (d3 >>> 51)) +
      p25519 * (d4.toNat / 2 ^ 51) =
      fe51Val d0 d1 d2 d3 d4 := by
    unfold fe51Val p25519
    rw [umaddl19_lsr51_toNat, add_mask51_lsr51_toNat, add_mask51_lsr51_toNat,
      add_mask51_lsr51_toNat, add_mask51_lsr51_toNat]
    omega
  rw [← hid, Nat.add_mul_mod_self_left]

theorem fe51Neg_val_mod (l0 l1 l2 l3 l4 : BitVec 64)
    (h : l0.toNat < 2 ^ 54 ∧ l1.toNat < 2 ^ 54 ∧ l2.toNat < 2 ^ 54 ∧
         l3.toNat < 2 ^ 54 ∧ l4.toNat < 2 ^ 54) :
    fe51Val
      (36028797018963664#64 - l0)
      (36028797018963952#64 - l1)
      (36028797018963952#64 - l2)
      (36028797018963952#64 - l3)
      (36028797018963952#64 - l4) % p25519 =
    fpNeg (fe51Val l0 l1 l2 l3 l4 % p25519) := by
  rcases h with ⟨h0, h1, h2, h3, h4⟩
  have hs0 : (36028797018963664#64 - l0).toNat = 36028797018963664 - l0.toNat := by
    rw [BitVec.toNat_sub_of_le (by change l0.toNat ≤ 36028797018963664; omega)]; rfl
  have hs1 : (36028797018963952#64 - l1).toNat = 36028797018963952 - l1.toNat := by
    rw [BitVec.toNat_sub_of_le (by change l1.toNat ≤ 36028797018963952; omega)]; rfl
  have hs2 : (36028797018963952#64 - l2).toNat = 36028797018963952 - l2.toNat := by
    rw [BitVec.toNat_sub_of_le (by change l2.toNat ≤ 36028797018963952; omega)]; rfl
  have hs3 : (36028797018963952#64 - l3).toNat = 36028797018963952 - l3.toNat := by
    rw [BitVec.toNat_sub_of_le (by change l3.toNat ≤ 36028797018963952; omega)]; rfl
  have hs4 : (36028797018963952#64 - l4).toNat = 36028797018963952 - l4.toNat := by
    rw [BitVec.toNat_sub_of_le (by change l4.toNat ≤ 36028797018963952; omega)]; rfl
  have hval :
      fe51Val
        (36028797018963664#64 - l0)
        (36028797018963952#64 - l1)
        (36028797018963952#64 - l2)
        (36028797018963952#64 - l3)
        (36028797018963952#64 - l4) =
      16 * p25519 - fe51Val l0 l1 l2 l3 l4 := by
    unfold fe51Val p25519
    rw [hs0, hs1, hs2, hs3, hs4]
    omega
  rw [hval]
  unfold fpNeg
  have hlt : fe51Val l0 l1 l2 l3 l4 < 16 * p25519 := by
    unfold fe51Val p25519; omega
  have hdiv : fe51Val l0 l1 l2 l3 l4 =
      p25519 * (fe51Val l0 l1 l2 l3 l4 / p25519) + fe51Val l0 l1 l2 l3 l4 % p25519 :=
    (Nat.div_add_mod _ _).symm
  have hq : fe51Val l0 l1 l2 l3 l4 / p25519 ≤ 15 := by
    unfold p25519 at hlt ⊢; omega
  have hmod_lt : fe51Val l0 l1 l2 l3 l4 % p25519 < p25519 :=
    Nat.mod_lt _ (by unfold p25519; omega)
  have hmod2 : (fe51Val l0 l1 l2 l3 l4 % p25519) % p25519 = fe51Val l0 l1 l2 l3 l4 % p25519 :=
    Nat.mod_eq_of_lt hmod_lt
  rw [hmod2]
  have hrew : 16 * p25519 - fe51Val l0 l1 l2 l3 l4 =
      (p25519 - fe51Val l0 l1 l2 l3 l4 % p25519) + p25519 * (15 - fe51Val l0 l1 l2 l3 l4 / p25519) := by
    unfold p25519 at hdiv hq hmod_lt ⊢
    omega
  rw [hrew, Nat.add_mul_mod_self_left]

/-! ## The selected entry -/

theorem sel_chain (tb : List (BitVec 8)) (x : BitVec 8) :
    (fe51Val (selAcc tb x 8 0) (selAcc tb x 8 1) (selAcc tb x 8 2) (selAcc tb x 8 3) (selAcc tb x 8 4) % p25519,
     fe51Val (selAcc tb x 8 5) (selAcc tb x 8 6) (selAcc tb x 8 7) (selAcc tb x 8 8) (selAcc tb x 8 9) % p25519,
     fe51Val (selAcc tb x 8 10) (selAcc tb x 8 11) (selAcc tb x 8 12) (selAcc tb x 8 13) (selAcc tb x 8 14) % p25519) =
    (if x == 8#8 || x == -8#8 then edTableEntryAt tb 7
    else if x == 7#8 || x == -7#8 then edTableEntryAt tb 6
    else if x == 6#8 || x == -6#8 then edTableEntryAt tb 5
    else if x == 5#8 || x == -5#8 then edTableEntryAt tb 4
    else if x == 4#8 || x == -4#8 then edTableEntryAt tb 3
    else if x == 3#8 || x == -3#8 then edTableEntryAt tb 2
    else if x == 2#8 || x == -2#8 then edTableEntryAt tb 1
    else if x == 1#8 || x == -1#8 then edTableEntryAt tb 0
    else (1, 1, 0)) := by
  simp only [selAcc, selC, Nat.reduceAdd, Nat.reduceMul]
  by_cases c8 : (x == 8#8 || x == -8#8) = true
  · simp only [c8, if_true, edTableEntryAt, fe51ValAt, Nat.reduceAdd, Nat.reduceMul]
  simp only [c8, Bool.false_eq_true, if_false]
  by_cases c7 : (x == 7#8 || x == -7#8) = true
  · simp only [c7, if_true, edTableEntryAt, fe51ValAt, Nat.reduceAdd, Nat.reduceMul]
  simp only [c7, Bool.false_eq_true, if_false]
  by_cases c6 : (x == 6#8 || x == -6#8) = true
  · simp only [c6, if_true, edTableEntryAt, fe51ValAt, Nat.reduceAdd, Nat.reduceMul]
  simp only [c6, Bool.false_eq_true, if_false]
  by_cases c5 : (x == 5#8 || x == -5#8) = true
  · simp only [c5, if_true, edTableEntryAt, fe51ValAt, Nat.reduceAdd, Nat.reduceMul]
  simp only [c5, Bool.false_eq_true, if_false]
  by_cases c4 : (x == 4#8 || x == -4#8) = true
  · simp only [c4, if_true, edTableEntryAt, fe51ValAt, Nat.reduceAdd, Nat.reduceMul]
  simp only [c4, Bool.false_eq_true, if_false]
  by_cases c3 : (x == 3#8 || x == -3#8) = true
  · simp only [c3, if_true, edTableEntryAt, fe51ValAt, Nat.reduceAdd, Nat.reduceMul]
  simp only [c3, Bool.false_eq_true, if_false]
  by_cases c2 : (x == 2#8 || x == -2#8) = true
  · simp only [c2, if_true, edTableEntryAt, fe51ValAt, Nat.reduceAdd, Nat.reduceMul]
  simp only [c2, Bool.false_eq_true, if_false]
  by_cases c1 : (x == 1#8 || x == -1#8) = true
  · simp only [c1, if_true, edTableEntryAt, fe51ValAt, Nat.reduceAdd, Nat.reduceMul]
  simp only [c1, Bool.false_eq_true, if_false]
  decide

/-! ## The postcondition from the 15 output words -/

theorem final_post (tb res : List (BitVec 8)) (x : BitVec 8) (c : Bool) (hc : x.msb = c)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : BitVec 64)
    (hb : a0.toNat < 2 ^ 53 ∧ a1.toNat < 2 ^ 53 ∧ a2.toNat < 2 ^ 53 ∧ a3.toNat < 2 ^ 53 ∧
      a4.toNat < 2 ^ 53 ∧ a5.toNat < 2 ^ 53 ∧ a6.toNat < 2 ^ 53 ∧ a7.toNat < 2 ^ 53 ∧
      a8.toNat < 2 ^ 53 ∧ a9.toNat < 2 ^ 53 ∧ a10.toNat < 2 ^ 53 ∧ a11.toNat < 2 ^ 53 ∧
      a12.toNat < 2 ^ 53 ∧ a13.toNat < 2 ^ 53 ∧ a14.toNat < 2 ^ 53)
    (hch : (fe51Val a0 a1 a2 a3 a4 % p25519, fe51Val a5 a6 a7 a8 a9 % p25519,
        fe51Val a10 a11 a12 a13 a14 % p25519) =
      (if x == 8#8 || x == -8#8 then edTableEntryAt tb 7
      else if x == 7#8 || x == -7#8 then edTableEntryAt tb 6
      else if x == 6#8 || x == -6#8 then edTableEntryAt tb 5
      else if x == 5#8 || x == -5#8 then edTableEntryAt tb 4
      else if x == 4#8 || x == -4#8 then edTableEntryAt tb 3
      else if x == 3#8 || x == -3#8 then edTableEntryAt tb 2
      else if x == 2#8 || x == -2#8 then edTableEntryAt tb 1
      else if x == 1#8 || x == -1#8 then edTableEntryAt tb 0
      else (1, 1, 0)))
    (h0 : ByteSlice.readLE res 0 8 = if c = true then a5 else a0)
    (h1 : ByteSlice.readLE res 8 8 = if c = true then a6 else a1)
    (h2 : ByteSlice.readLE res 16 8 = if c = true then a7 else a2)
    (h3 : ByteSlice.readLE res 24 8 = if c = true then a8 else a3)
    (h4 : ByteSlice.readLE res 32 8 = if c = true then a9 else a4)
    (h5 : ByteSlice.readLE res 40 8 = if c = true then a0 else a5)
    (h6 : ByteSlice.readLE res 48 8 = if c = true then a1 else a6)
    (h7 : ByteSlice.readLE res 56 8 = if c = true then a2 else a7)
    (h8 : ByteSlice.readLE res 64 8 = if c = true then a3 else a8)
    (h9 : ByteSlice.readLE res 72 8 = if c = true then a4 else a9)
    (h10 : ByteSlice.readLE res 80 8 = if c = true then nd0 a10 a14 else a10)
    (h11 : ByteSlice.readLE res 88 8 = if c = true then nd1 a11 a10 else a11)
    (h12 : ByteSlice.readLE res 96 8 = if c = true then ndk a12 a11 else a12)
    (h13 : ByteSlice.readLE res 104 8 = if c = true then ndk a13 a12 else a13)
    (h14 : ByteSlice.readLE res 112 8 = if c = true then ndk a14 a13 else a14) :
    fe51AffineNielsBoundedAt res 0 (2 ^ 53) ∧
      (fe51ValAt res 0 % p25519, fe51ValAt res 40 % p25519, fe51ValAt res 80 % p25519) =
        edSelectAffineNiels tb x := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩ := hb
  unfold fe51AffineNielsBoundedAt fe51LimbsBoundedAt fe51ValAt edSelectAffineNiels
  simp only [Nat.reduceAdd, Nat.zero_add]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, ← hch, hc]
  cases c
  · simp only [Bool.false_eq_true, if_false, and_true]
    exact ⟨⟨b0, b1, b2, b3, b4⟩, ⟨b5, b6, b7, b8, b9⟩, b10, b11, b12, b13, b14⟩
  · simp only [if_true]
    have hr := fe51Reduce_bounded (36028797018963664#64 - a10) (36028797018963952#64 - a11)
      (36028797018963952#64 - a12) (36028797018963952#64 - a13) (36028797018963952#64 - a14)
    simp only [nd0, nd1, ndk]
    have l : (2 : Nat) ^ 52 ≤ 2 ^ 53 := by norm_num
    refine ⟨⟨⟨b5, b6, b7, b8, b9⟩, ⟨b0, b1, b2, b3, b4⟩, lt_of_lt_of_le hr.1 l, lt_of_lt_of_le hr.2.1 l,
      lt_of_lt_of_le hr.2.2.1 l, lt_of_lt_of_le hr.2.2.2.1 l, lt_of_lt_of_le hr.2.2.2.2 l⟩, ?_⟩
    rw [fe51Reduce_val_mod, fe51Neg_val_mod _ _ _ _ _ ⟨by omega, by omega, by omega, by omega, by omega⟩]

end X25519Dalek.ESel
end

section
/-! # Byte slices as memory regions, and merging adjacent regions

`bytes_shape` and `bytes_memRegion` follow `Solutions/X25519DalekField/G/Region.lean` (sibling batch
q447-xd-goal, after DeepMind's ProofLib); restated with the EF framework's heap lemmas. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.ESel

open Arm64 Arm64.Obj

theorem regionHeap_phys' (base : BitVec 64) (len : Nat) (m : Memory) (y : BitVec 64) :
    (regionHeap base len m).phys y =
      if (y - base).toNat < len then some (.rw (m.read8 y)) else none := by
  unfold regionHeap InRegion; exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem bytes_shape : ∀ {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap},
    (a ↦ₛ bs).holds h →
      h.auth = (fun _ _ => none) ∧ h.frag = (fun _ _ => none) ∧ h.mapped = (fun _ => false) ∧
      ∀ y, bs.length ≤ (y - a).toNat → h.phys y = none
  | a, [], h, hh => by
    simp only [pointsToBytes] at hh
    change h = Heap.empty at hh
    subst hh
    exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  | a, b :: bs, h, hh => by
    simp only [pointsToBytes] at hh
    obtain ⟨h1, h2, _, rfl, h1e, h2h⟩ := hh
    change h1 = Heap.singleton a b at h1e
    subst h1e
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

theorem bytes_memRegion (a : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦ₛ bs) ⊢ memRegion a bs.length := by
  intro h hh
  obtain ⟨ha, hf, hm, hp⟩ := bytes_shape hh
  refine ⟨Memory.ofFn (fun y => bs.getD (y - a).toNat 0), ?_⟩
  show h = regionHeap a bs.length _
  apply Heap.ext
  · funext y
    rw [regionHeap_phys']
    split
    · rename_i hy
      have := rwCells_bytes bs a h hh (y - a).toNat hy
      rw [show a + BitVec.ofNat 64 (y - a).toNat = y by bv_omega] at this
      rw [this]
      simp only [Memory.read8, Memory.ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy,
        Option.getD_some]
    · rename_i hy; exact hp y (by omega)
  · exact ha
  · exact hf
  · exact hm

theorem read8_ofFn (f : BitVec 64 → BitVec 8) (y : BitVec 64) : (Memory.ofFn f).read8 y = f y := rfl

theorem region_merge (a : BitVec 64) (n k : Nat) (hnk : n + k < 2 ^ 64) :
    (memRegion a n ∗ memRegion (a + BitVec.ofNat 64 n) k) ⊢ memRegion a (n + k) := by
  rintro _ ⟨h1, h2, _, rfl, ⟨mm1, e1⟩, ⟨mm2, e2⟩⟩
  change h1 = regionHeap a n mm1 at e1
  change h2 = regionHeap (a + BitVec.ofNat 64 n) k mm2 at e2
  subst e1 e2
  refine ⟨Memory.ofFn (fun y => if (y - a).toNat < n then mm1.read8 y else mm2.read8 y), ?_⟩
  show _ = regionHeap a (n + k) _
  apply Heap.ext
  · funext y
    simp only [Heap.union, regionHeap_phys']
    have e : ¬ (y - a).toNat < n → ((y - (a + BitVec.ofNat 64 n)).toNat < k ↔ (y - a).toNat < n + k) := by
      intro hy; constructor <;> intro h <;> bv_omega
    by_cases hy : (y - a).toNat < n
    · have hy2 : (y - a).toNat < n + k := by omega
      simp only [hy, hy2, if_true, read8_ofFn]
    · by_cases hy2 : (y - a).toNat < n + k
      · have hy3 := (e hy).mpr hy2
        simp only [hy, hy2, hy3, if_true, if_false, read8_ofFn]
      · have hy3 : ¬ (y - (a + BitVec.ofNat 64 n)).toNat < k := fun h => hy2 ((e hy).mp h)
        simp only [hy, hy2, hy3, if_false]
  · rfl
  · rfl
  · funext y; simp [Heap.union, regionHeap]

/-! ## A region as two regions, the second as its bytes -/

theorem regionHeap_union (a : BitVec 64) (n k : Nat) (hnk : n + k < 2 ^ 64) (mm : Memory) :
    (regionHeap a n mm).union (regionHeap (a + BitVec.ofNat 64 n) k mm) = regionHeap a (n + k) mm := by
  apply Heap.ext
  · funext y
    simp only [Heap.union, regionHeap_phys']
    have e : ¬ (y - a).toNat < n → ((y - (a + BitVec.ofNat 64 n)).toNat < k ↔ (y - a).toNat < n + k) := by
      intro hy; constructor <;> intro h <;> bv_omega
    by_cases hy : (y - a).toNat < n
    · have hy2 : (y - a).toNat < n + k := by omega
      simp only [hy, hy2, if_true]
    · by_cases hy2 : (y - a).toNat < n + k
      · have hy3 := (e hy).mpr hy2
        simp only [hy, hy2, hy3, if_true, if_false]
      · have hy3 : ¬ (y - (a + BitVec.ofNat 64 n)).toNat < k := fun h => hy2 ((e hy).mp h)
        simp only [hy, hy2, hy3, if_false]
  · rfl
  · rfl
  · funext y; simp [Heap.union, regionHeap]

theorem regionHeap_disjoint (a : BitVec 64) (n k : Nat) (hnk : n + k < 2 ^ 64) (mm : Memory) :
    (regionHeap a n mm).Disjoint (regionHeap (a + BitVec.ofNat 64 n) k mm) := by
  refine ⟨fun y => ?_, fun γ k => Or.inl rfl, fun γ k => Or.inl rfl, ?_, fun y => Or.inl rfl⟩
  · simp only [regionHeap_phys']
    by_cases hy : (y - a).toNat < n
    · right; left
      have : ¬ (y - (a + BitVec.ofNat 64 n)).toNat < k := by bv_omega
      rw [if_neg this]
    · left; rw [if_neg hy]
  · intro γ k oa v h
    rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h

theorem bytesAt_holds : ∀ (n : Nat) (a : BitVec 64) (m : Memory), n < 2 ^ 64 →
    (a ↦ₛ bytesAt m a n).holds (regionHeap a n m)
  | 0, a, m, _ => by
    show _ = _
    apply Heap.ext
    · funext y; simp [regionHeap, InRegion, Heap.empty]
    · rfl
    · rfl
    · rfl
  | n + 1, a, m, hn => by
    rw [bytesAt_succ]
    have ih := bytesAt_holds n (a + 1#64) m (by omega)
    refine ⟨Heap.singleton a (m.read8 a), regionHeap (a + 1#64) n m, ?_, ?_, rfl, ih⟩
    · refine ⟨fun y => ?_, fun γ k => Or.inl rfl, fun γ k => Or.inl rfl, ?_, fun y => Or.inl rfl⟩
      · by_cases hy : y = a
        · subst hy; right; left
          rw [regionHeap_phys', if_neg]; bv_omega
        · left; simp [Heap.singleton, hy]
      · intro γ k oa v h
        rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
    · apply Heap.ext
      · funext y
        by_cases hy : y = a
        · subst hy
          simp only [Heap.union, Heap.singleton, if_true, regionHeap_phys']
          rw [if_pos (by bv_omega)]
        · simp only [Heap.union, Heap.singleton, hy, if_false, regionHeap_phys']
          have e : ((y - a).toNat < n + 1) ↔ ((y - (a + 1#64)).toNat < n) := by
            constructor <;> intro h <;> bv_omega
          by_cases hc : (y - (a + 1#64)).toNat < n
          · rw [if_pos (e.mpr hc), if_pos hc]
          · rw [if_neg (fun h => hc (e.mp h)), if_neg hc]
      · rfl
      · rfl
      · funext y; simp [Heap.union, Heap.singleton, regionHeap]

/-- A refreshed frame of `n + k` bytes is a frame of `n` bytes and the `k` current bytes above it. -/
theorem rf_region_split (m : Memory) (a : BitVec 64) (n k : Nat) (hnk : n + k < 2 ^ 64) :
    Rf m (memRegion a (n + k))
      (memRegion a n ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bytesAt m (a + BitVec.ofNat 64 n) k)) := by
  rintro h ⟨mm, rfl⟩
  have e : refresh m (regionHeap a (n + k) mm) = regionHeap a (n + k) m := by
    simp only [refresh, regionHeap]
    congr 1; funext y
    split <;> simp_all
  change (memRegion a n ∗ _).holds (refresh m (regionHeap a (n + k) mm))
  rw [e, ← regionHeap_union a n k hnk m]
  exact ⟨_, _, regionHeap_disjoint a n k hnk m, rfl, ⟨m, rfl⟩, bytesAt_holds k _ m (by omega)⟩

theorem sat_mono_left {m : Memory} {P P' R : SepProp} (hs : m ⊨ P ∗ R) (h : P ⊢ P') : m ⊨ P' ∗ R := by
  obtain ⟨hh, ⟨h1, h2, hd, rfl, p, r⟩, hm⟩ := hs
  exact ⟨_, ⟨h1, h2, hd, rfl, h _ p, r⟩, hm⟩

theorem sep_mono {P P' Q Q' : SepProp} (h1 : P ⊢ P') (h2 : Q ⊢ Q') : (P ∗ Q) ⊢ (P' ∗ Q') := by
  rintro _ ⟨a, b, hd, rfl, p, q⟩
  exact ⟨a, b, hd, rfl, h1 _ p, h2 _ q⟩

theorem ent_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q := fun _ hp => h ▸ hp

end X25519Dalek.ESel
end

section
/-! # `LookupTable<AffineNielsPoint>::select` (block 6): the loop and the contract -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.ESel

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj

/-! ## Owned bytes of the three straight-line parts -/

theorem wacc1 (S : BitVec 64) : ∀ c : BitVec 64, (24 ≤ c.toNat ∧ c.toNat + 8 ≤ 80) →
    AllB (InRegion (S + 24#64) 56) (S + c) 8 := by
  intro c hc j hj
  unfold InRegion
  rw [show S + c + BitVec.ofNat 64 j - (S + 24#64) = c + BitVec.ofNat 64 j - 24#64 by abel]
  bv_omega

theorem wacc2 (S : BitVec 64) : ∀ c1 c2 : BitVec 64, (24 ≤ (c1 + c2).toNat ∧ (c1 + c2).toNat + 8 ≤ 80) →
    AllB (InRegion (S + 24#64) 56) (S + c1 + c2) 8 := by
  intro c1 c2 hc; rw [BitVec.add_assoc]; exact wacc1 S _ hc

theorem wsub (S a : BitVec 64) (h : InRegion (S + 24#64) 56 a) : InRegion S 176 a := by
  unfold InRegion at h ⊢
  rw [show a - S = (a - (S + 24#64)) + 24#64 by abel]
  bv_omega

theorem wstk1 (S : BitVec 64) : ∀ c : BitVec 64, c.toNat + 8 ≤ 176 → AllB (InRegion S 176) (S + c) 8 := by
  intro c hc j hj
  unfold InRegion
  rw [show S + c + BitVec.ofNat 64 j - S = c + BitVec.ofNat 64 j by abel]
  bv_omega

theorem wstk2 (S : BitVec 64) : ∀ c1 c2 : BitVec 64, (c1 + c2).toNat + 8 ≤ 176 →
    AllB (InRegion S 176) (S + c1 + c2) 8 := by
  intro c1 c2 hc; rw [BitVec.add_assoc]; exact wstk1 S _ hc

theorem wstk3 (S : BitVec 64) : ∀ c1 c2 c3 : BitVec 64, (c1 + c2 + c3).toNat + 8 ≤ 176 →
    AllB (InRegion S 176) (S + c1 + c2 + c3) 8 := by
  intro c1 c2 c3 hc; rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.add_assoc c1]; exact wstk1 S _ hc

theorem wout1 (O : BitVec 64) : ∀ c : BitVec 64, c.toNat + 8 ≤ 120 → AllB (InRegion O 120) (O + c) 8 := by
  intro c hc j hj
  unfold InRegion
  rw [show O + c + BitVec.ofNat 64 j - O = c + BitVec.ofNat 64 j by abel]
  bv_omega

theorem wout2 (O : BitVec 64) : ∀ c1 c2 : BitVec 64, (c1 + c2).toNat + 8 ≤ 120 →
    AllB (InRegion O 120) (O + c1 + c2) 8 := by
  intro c1 c2 hc; rw [BitVec.add_assoc]; exact wout1 O _ hc

theorem fixB_of_all {m m' : Memory} {S : BitVec 64}
    (h : ∀ i, i < 176 → m'.read8 (S + BitVec.ofNat 64 i) = m.read8 (S + BitVec.ofNat 64 i)) :
    FixB m m' S := fun i hi _ => h i hi

theorem fixB_of_memOK {m m' : Memory} {S : BitVec 64} (hok : MemOK m (InRegion (S + 24#64) 56) m') :
    FixB m m' S := by
  intro i hi hio
  refine (hok _).2.2.2 ?_
  unfold InRegion
  rw [show S + BitVec.ofNat 64 i - (S + 24#64) = BitVec.ofNat 64 i - 24#64 by abel]
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-! ## The table -/

theorem tbl_bytes {m : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hmi : MI m S O T tb R) {W : BitVec 64 → Prop}
    (hWs : ∀ a, W a → InRegion S 176 a ∨ InRegion O 120 a) :
    ∀ i (hi : i < tb.length), m.read8 (T + BitVec.ofNat 64 i) = tb[i] ∧
      (m.perm (T + BitVec.ofNat 64 i)).r = true ∧ m.isLazyFree (T + BitVec.ofNat 64 i) = false ∧
      ¬ W (T + BitVec.ofNat 64 i) := by
  intro i hi
  obtain ⟨a, b, c, d⟩ := mi_tbl hmi i hi
  exact ⟨a, b, c, fun hw => d (hWs _ hw)⟩

theorem tbl_addr (T : BitVec 64) (j k : Nat) (c : BitVec 64) (hc : c + 56#64 = BitVec.ofNat 64 (8 * k)) :
    T + BitVec.ofNat 64 (120 * j + 56) + c = T + BitVec.ofNat 64 (120 * j + 8 * k) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_add, ← hc]
  congr 1
  abel

theorem tbl_fact {m0 : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hmi : MI m0 S O T tb R) {W : BitVec 64 → Prop}
    (hWs : ∀ a, W a → InRegion S 176 a ∨ InRegion O 120 a) (htl : tb.length = 960)
    (j k : Nat) (hjk : 120 * j + 8 * k + 8 ≤ 960) (c : BitVec 64)
    (hc : c + 56#64 = BitVec.ofNat 64 (8 * k)) :
    ∀ m', MemOK m0 W m' → m'.read64 (T + BitVec.ofNat 64 (120 * j + 56) + c) =
      ByteSlice.readLE tb (120 * j + 8 * k) 8 := by
  intro m' hok
  rw [tbl_addr T j k c hc]
  exact read64_buf (tbl_bytes hmi hWs) hok _ (by omega)

theorem tbl_fact7 {m0 : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hmi : MI m0 S O T tb R) {W : BitVec 64 → Prop}
    (hWs : ∀ a, W a → InRegion S 176 a ∨ InRegion O 120 a) (htl : tb.length = 960)
    (j : Nat) (hj : j < 8) :
    ∀ m', MemOK m0 W m' → m'.read64 (T + BitVec.ofNat 64 (120 * j + 56)) =
      ByteSlice.readLE tb (120 * j + 8 * 7) 8 := by
  intro m' hok
  exact read64_buf (tbl_bytes hmi hWs) hok _ (by omega)

theorem tbl_cr {m0 : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hmi : MI m0 S O T tb R) {W : BitVec 64 → Prop}
    (hWs : ∀ a, W a → InRegion S 176 a ∨ InRegion O 120 a) (htl : tb.length = 960)
    (j : Nat) (hj : j < 8) :
    ∀ m', MemOK m0 W m' → ∀ c : BitVec 64, (c + 56#64).toNat + 8 ≤ 120 →
      m'.canRead (T + BitVec.ofNat 64 (120 * j + 56) + c) 8 = true := by
  intro m' hok c hc
  have e : T + BitVec.ofNat 64 (120 * j + 56) + c = T + BitVec.ofNat 64 (120 * j + (c + 56#64).toNat) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    congr 1; abel
  rw [e]
  exact canRead_buf (tbl_bytes hmi hWs) hok _ (by omega)

theorem tbl_cr2 {m0 : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hmi : MI m0 S O T tb R) {W : BitVec 64 → Prop}
    (hWs : ∀ a, W a → InRegion S 176 a ∨ InRegion O 120 a) (htl : tb.length = 960)
    (j : Nat) (hj : j < 8) :
    ∀ m', MemOK m0 W m' → ∀ c : BitVec 64, (c + 64#64).toNat + 8 ≤ 120 →
      m'.canRead (T + BitVec.ofNat 64 (120 * j + 56) + c + 8#64) 8 = true := by
  intro m' hok c hc
  rw [BitVec.add_assoc _ c]
  refine tbl_cr hmi hWs htl j hj m' hok _ ?_
  rwa [BitVec.add_assoc, show (8#64 : BitVec 64) + 56#64 = 64#64 from rfl]

/-! ## Registers after a call -/

theorem reach_of_sf {mpl : MultiPlacement} {i : Nat} {P : State → Prop} {sf : State}
    {pc sp : BitVec 64} (hpc : sf.pc = pc) (hsp : sf.sp = sp)
    (h : Reach mpl i P (mkS sf pc (regL [sf.regs.regs 0#5, sf.regs.regs 1#5, sf.regs.regs 2#5,
      sf.regs.regs 3#5, sf.regs.regs 4#5, sf.regs.regs 5#5, sf.regs.regs 6#5, sf.regs.regs 7#5,
      sf.regs.regs 8#5, sf.regs.regs 9#5, sf.regs.regs 10#5, sf.regs.regs 11#5, sf.regs.regs 12#5,
      sf.regs.regs 13#5, sf.regs.regs 14#5, sf.regs.regs 15#5, sf.regs.regs 16#5, sf.regs.regs 17#5,
      sf.regs.regs 18#5, sf.regs.regs 19#5, sf.regs.regs 20#5, sf.regs.regs 21#5, sf.regs.regs 22#5,
      sf.regs.regs 23#5, sf.regs.regs 24#5, sf.regs.regs 25#5, sf.regs.regs 26#5, sf.regs.regs 27#5,
      sf.regs.regs 28#5, sf.regs.regs 29#5, sf.regs.regs 30#5, sf.regs.regs 31#5]) sp sf.mem sf.pstate)) :
    Reach mpl i P sf := by
  rw [← regL_init, ← hpc, ← hsp] at h; exact h

theorem and255 {v : BitVec 64} {c : Bool}
    (h : v.truncate 8 = (if c = true then 1#64 else 0#64).truncate 8) :
    v &&& 255#64 = if c = true then 1#64 else 0#64 := by
  have e : v &&& 255#64 = (v.truncate 8).zeroExtend 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hm := (by decide : ∀ k (hk : k < 64), (255#64).getLsbD k = decide (k < 8)) i hi
    simp only [BitVec.getLsbD_and, hm, BitVec.getLsbD_setWidth]
    by_cases h8 : i < 8 <;> simp [h8, hi]
  rw [e, h]; cases c <;> rfl

/-! ## The loop invariant -/

/-- After `j` iterations, at the loop head: the accumulators hold `selAcc tb x j`. -/
def LInv (mpl : MultiPlacement) (s0 : State) (R : SepProp) (S O T X : BitVec 64)
    (tb : List (BitVec 8)) (sv : BitVec 5 → BitVec 64) (j : Nat) (sb : State)
    (r : BitVec 5 → BitVec 64) (m : Memory) : Prop :=
  sb.status = .Running ∧ calleeSavedVRegs sb = calleeSavedVRegs s0 ∧
  x25519CliMultiLib.CodeLoaded mpl m ∧ MI m S O T tb R ∧ Fx m S X sv ∧
  Acc m S (selAcc tb (X.truncate 8) j 1) (selAcc tb (X.truncate 8) j 2) (selAcc tb (X.truncate 8) j 3)
    (selAcc tb (X.truncate 8) j 4) (selAcc tb (X.truncate 8) j 7) (selAcc tb (X.truncate 8) j 8)
    (selAcc tb (X.truncate 8) j 9) ∧
  r 19#5 = selAcc tb (X.truncate 8) j 12 ∧ r 20#5 = selAcc tb (X.truncate 8) j 11 ∧
  r 21#5 = selAcc tb (X.truncate 8) j 0 ∧ r 22#5 = selAcc tb (X.truncate 8) j 6 ∧
  r 23#5 = selAcc tb (X.truncate 8) j 5 ∧ r 24#5 = selAcc tb (X.truncate 8) j 10 ∧
  r 25#5 = T + BitVec.ofNat 64 (120 * j + 56) ∧ r 26#5 = BitVec.ofNat 64 (j + 1) ∧
  r 27#5 = selAcc tb (X.truncate 8) j 14 ∧ r 28#5 = selAcc tb (X.truncate 8) j 13 ∧
  r 29#5 = S + 80#64

theorem z_iter (j : Nat) (hj : j < 8) :
    decide (BitVec.ofNat 64 (j + 1) + 1#64 = 9#64) = decide (j + 1 = 8) := by
  interval_cases j <;> decide

theorem pc_iter (B : BitVec 64) (j : Nat) :
    (if decide (j + 1 = 8) = true then B + BitVec.ofNat 64 (420 + 4)
      else B + BitVec.ofNat 64 420 + 0xfffffffffffffecc#64) =
    B + BitVec.ofNat 64 (if j + 1 = 8 then 424 else 112) := by
  by_cases h8 : j + 1 = 8
  · simp [h8]
  · simp only [h8, decide_false, Bool.false_eq_true, if_false, BitVec.add_assoc, BitVec.reduceAdd]

theorem x25_iter (T : BitVec 64) (j : Nat) :
    T + BitVec.ofNat 64 (120 * j + 56) + 120#64 = T + BitVec.ofNat 64 (120 * (j + 1) + 56) := by
  rw [BitVec.add_assoc, show (120#64 : BitVec 64) = BitVec.ofNat 64 120 from rfl, ← BitVec.ofNat_add]
  congr 2 <;> ring

theorem x26_iter (j : Nat) : BitVec.ofNat 64 (j + 1) + 1#64 = BitVec.ofNat 64 (j + 1 + 1) := by
  rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]

theorem loop_iter {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s0 : State}
    {R : SepProp} {S O T X : BitVec 64} {tb : List (BitVec 8)} {sv : BitVec 5 → BitVec 64}
    {Q : State → Prop} (hsp : S.toNat % 16 = 0) (htl : tb.length = 960)
    (j : Nat) (hj : j < 8) {sb : State} {r : BitVec 5 → BitVec 64} {m : Memory} {ps : PState}
    (hI : LInv mpl s0 R S O T X tb sv j sb r m)
    (hnext : ∀ sb' r' m' ps', LInv mpl s0 R S O T X tb sv (j + 1) sb' r' m' →
      Reach mpl 6 Q (mkS sb' (mpl.base 6 + BitVec.ofNat 64 (if j + 1 = 8 then 424 else 112)) r' S m' ps')) :
    Reach mpl 6 Q (mkS sb (mpl.base 6 + BitVec.ofNat 64 112) r S m ps) := by
  obtain ⟨hrun, hvr, hCL, hmi, hfx, hacc, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩ := hI
  have hWs : ∀ a, InRegion (S + 24#64) 56 a → InRegion S 176 a ∨ InRegion O 120 a :=
    fun a h => Or.inl (wsub S a h)
  rw [regL_init r, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
  refine pre_run (hCL 6 (by decide)) hrun (mi_wowned hmi hWs) (memOK_refl m _) hsp (mi_rd1 hmi)
    (mi_rd2 hmi) hfx.2.2.1 hfx.2.2.2.1 ?_
  intro a8 a9 ps1
  refine call_bb hP hrun hCL (f06_132 hP (hCL 6 (by decide))) hsp (mi_pre_call hmi) ?_
  intro sf hrunf hpcf hspf hkept hvrf hCLf hmemf hx0
  obtain ⟨hmif, hbytes⟩ := mi_call hmemf
  have k19 : sf.regs.regs 19#5 = selAcc tb (X.truncate 8) j 12 := hkept 19#5 (by decide) (by decide)
  have k20 : sf.regs.regs 20#5 = selAcc tb (X.truncate 8) j 11 := hkept 20#5 (by decide) (by decide)
  have k21 : sf.regs.regs 21#5 = selAcc tb (X.truncate 8) j 0 := hkept 21#5 (by decide) (by decide)
  have k22 : sf.regs.regs 22#5 = selAcc tb (X.truncate 8) j 6 := hkept 22#5 (by decide) (by decide)
  have k23 : sf.regs.regs 23#5 = selAcc tb (X.truncate 8) j 5 := hkept 23#5 (by decide) (by decide)
  have k24 : sf.regs.regs 24#5 = selAcc tb (X.truncate 8) j 10 := hkept 24#5 (by decide) (by decide)
  have k25 : sf.regs.regs 25#5 = T + BitVec.ofNat 64 (120 * j + 56) := hkept 25#5 (by decide) (by decide)
  have k26 : sf.regs.regs 26#5 = BitVec.ofNat 64 (j + 1) := hkept 26#5 (by decide) (by decide)
  have k27 : sf.regs.regs 27#5 = selAcc tb (X.truncate 8) j 14 := hkept 27#5 (by decide) (by decide)
  have k28 : sf.regs.regs 28#5 = selAcc tb (X.truncate 8) j 13 := hkept 28#5 (by decide) (by decide)
  have k29 : sf.regs.regs 29#5 = S + 80#64 := hkept 29#5 (by decide) (by decide)
  have hq0 : sf.regs.regs 0#5 &&& 255#64 =
      if selC (X.truncate 8) (j + 1) = true then 1#64 else 0#64 := by
    apply and255
    rw [hx0, ← cz_sel X j hj]
    rfl
  have hacc' := acc_of_all hbytes hacc
  apply reach_of_sf hpcf hspf
  rw [k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29]
  have hCL6 : (prog mpl 6).CodeLoaded sf.mem := hCLf 6 (by decide)
  refine body_run hCL6 hrunf (mi_wowned hmif hWs) (memOK_refl _ _) hsp (wacc1 S) (wacc2 S)
    (mi_rd1 hmif) (mi_rd2 hmif) (mi_rd3 hmif)
    (tbl_cr hmif hWs htl j hj) (tbl_cr2 hmif hWs htl j hj)
    (tbl_fact hmif hWs htl j 0 (by omega) _ (by decide))
    (tbl_fact hmif hWs htl j 1 (by omega) _ (by decide))
    (tbl_fact hmif hWs htl j 2 (by omega) _ (by decide))
    (tbl_fact hmif hWs htl j 3 (by omega) _ (by decide))
    (tbl_fact hmif hWs htl j 4 (by omega) _ (by decide))
    (tbl_fact hmif hWs htl j 5 (by omega) _ (by decide))
    (tbl_fact hmif hWs htl j 6 (by omega) _ (by decide))
    (tbl_fact7 hmif hWs htl j hj)
    (tbl_fact hmif hWs htl j 8 (by omega) _ (by decide))
    (tbl_fact hmif hWs htl j 9 (by omega) _ (by decide))
    (tbl_fact hmif hWs htl j 10 (by omega) _ (by decide))
    (tbl_fact hmif hWs htl j 11 (by omega) _ (by decide))
    (tbl_fact hmif hWs htl j 12 (by omega) _ (by decide))
    (tbl_fact hmif hWs htl j 13 (by omega) _ (by decide))
    (tbl_fact hmif hWs htl j 14 (by omega) _ (by decide))
    hacc' hq0 ?_
  intro m' L' ps' hok' hz hacc2 g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29
  rw [z_iter j hj] at hz
  refine r_bne hz hrunf (mi_wowned hmif hWs) hok' (f06_420 hCL6) ?_
  rw [pc_iter]
  refine hnext sf (regL L') m' ps' ⟨hrunf, hvrf.trans hvr, libcl_memOK (mi_wowned hmif hWs) hok' hCLf,
    mi_frame hmif hok' hWs, fx_of_fixB (fixB_of_memOK hok') (fx_of_fixB (fixB_of_all hbytes) hfx),
    hacc2, g19, g20, g21, g22, g23, g24, ?_, ?_, g27, g28, g29⟩
  · rw [g25, x25_iter]
  · rw [g26, x26_iter]

theorem loop_all {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s0 : State}
    {R : SepProp} {S O T X : BitVec 64} {tb : List (BitVec 8)} {sv : BitVec 5 → BitVec 64}
    {Q : State → Prop} (hsp : S.toNat % 16 = 0) (htl : tb.length = 960)
    (hepi : ∀ sb r m ps, LInv mpl s0 R S O T X tb sv 8 sb r m →
      Reach mpl 6 Q (mkS sb (mpl.base 6 + BitVec.ofNat 64 424) r S m ps)) :
    ∀ n j, j + n + 1 = 8 → ∀ sb r m ps, LInv mpl s0 R S O T X tb sv j sb r m →
      Reach mpl 6 Q (mkS sb (mpl.base 6 + BitVec.ofNat 64 112) r S m ps) := by
  intro n
  induction n with
  | zero =>
    intro j hj sb r m ps hI
    refine loop_iter hP hsp htl j (by omega) hI fun sb' r' m' ps' hI' => ?_
    have e : j + 1 = 8 := by omega
    rw [if_pos e]; rw [e] at hI'; exact hepi sb' r' m' ps' hI'
  | succ n ih =>
    intro j hj sb r m ps hI
    refine loop_iter hP hsp htl j (by omega) hI fun sb' r' m' ps' hI' => ?_
    rw [if_neg (by omega)]
    exact ih (j + 1) (by omega) sb' r' m' ps' hI'

theorem mi_stk_notO {m : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hmi : MI m S O T tb R) (i : Nat) (hi : i < 176) : ¬ InRegion O 120 (S + BitVec.ofNat 64 i) := by
  intro hO
  obtain ⟨h, hh, -⟩ := hmi
  obtain ⟨hP, hR, -, rfl, p, -⟩ := hh
  obtain ⟨h1, h23, -, rfl, -, p23⟩ := p
  obtain ⟨hS, hrest, hd, rfl, pS, prest⟩ := p23
  have e1 := rwCells_bytes _ S hS pS i (by rw [bytesAt_length]; exact hi)
  have ea : S + BitVec.ofNat 64 i = O + BitVec.ofNat 64 ((S + BitVec.ofNat 64 i - O).toNat) := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; abel
  have e2 := cell_sep_left prest fun h4 p4 => rwCells_bytes _ O h4 p4 _ (by rw [bytesAt_length]; exact hO)
  rw [← ea] at e2
  rcases hd.1 (S + BitVec.ofNat 64 i) with e | e | ⟨b, e3, e4⟩
  · rw [e1] at e; cases e
  · rw [e2] at e; cases e
  · rw [e1] at e3; cases e3

theorem stk_fact {m0 : Memory} {S O T : BitVec 64} {tb : List (BitVec 8)} {R : SepProp}
    (hmi : MI m0 S O T tb R) (c : Nat) (hc : c + 8 ≤ 176) {v : BitVec 64}
    (hv : m0.read64 (S + BitVec.ofNat 64 c) = v) :
    ∀ m', MemOK m0 (InRegion O 120) m' → m'.read64 (S + BitVec.ofNat 64 c) = v := by
  intro m' hok
  rw [← hv]
  exact read64_memOK hok fun j hj => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact mi_stk_notO hmi _ (by omega)

theorem epi_from {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s0 : State}
    {R : SepProp} {S O T X : BitVec 64} {tb : List (BitVec 8)} {sv : BitVec 5 → BitVec 64}
    {Q : State → Prop} (hsp : S.toNat % 16 = 0) (hO : sv 0#5 = O)
    (hQ : ∀ (sf : State) (m' : Memory) (r' : BitVec 5 → BitVec 64), sf.status = .Running →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → MI m' S O T tb R →
      m'.read64 O = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 5 else selAcc tb (X.truncate 8) 8 0) →
      m'.read64 (O + 8#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 6 else selAcc tb (X.truncate 8) 8 1) →
      m'.read64 (O + 16#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 7 else selAcc tb (X.truncate 8) 8 2) →
      m'.read64 (O + 24#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 8 else selAcc tb (X.truncate 8) 8 3) →
      m'.read64 (O + 32#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 9 else selAcc tb (X.truncate 8) 8 4) →
      m'.read64 (O + 40#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 0 else selAcc tb (X.truncate 8) 8 5) →
      m'.read64 (O + 48#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 1 else selAcc tb (X.truncate 8) 8 6) →
      m'.read64 (O + 56#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 2 else selAcc tb (X.truncate 8) 8 7) →
      m'.read64 (O + 64#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 3 else selAcc tb (X.truncate 8) 8 8) →
      m'.read64 (O + 72#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 4 else selAcc tb (X.truncate 8) 8 9) →
      m'.read64 (O + 80#64) = (if X.getLsbD 7 = true then nd0 (selAcc tb (X.truncate 8) 8 10) (selAcc tb (X.truncate 8) 8 14) else selAcc tb (X.truncate 8) 8 10) →
      m'.read64 (O + 88#64) = (if X.getLsbD 7 = true then nd1 (selAcc tb (X.truncate 8) 8 11) (selAcc tb (X.truncate 8) 8 10) else selAcc tb (X.truncate 8) 8 11) →
      m'.read64 (O + 96#64) = (if X.getLsbD 7 = true then ndk (selAcc tb (X.truncate 8) 8 12) (selAcc tb (X.truncate 8) 8 11) else selAcc tb (X.truncate 8) 8 12) →
      m'.read64 (O + 104#64) = (if X.getLsbD 7 = true then ndk (selAcc tb (X.truncate 8) 8 13) (selAcc tb (X.truncate 8) 8 12) else selAcc tb (X.truncate 8) 8 13) →
      m'.read64 (O + 112#64) = (if X.getLsbD 7 = true then ndk (selAcc tb (X.truncate 8) 8 14) (selAcc tb (X.truncate 8) 8 13) else selAcc tb (X.truncate 8) 8 14) →
      r' 19#5 = sv 19#5 → r' 20#5 = sv 20#5 → r' 21#5 = sv 21#5 → r' 22#5 = sv 22#5 → r' 23#5 = sv 23#5 → r' 24#5 = sv 24#5 → r' 25#5 = sv 25#5 → r' 26#5 = sv 26#5 → r' 27#5 = sv 27#5 → r' 28#5 = sv 28#5 → r' 29#5 = sv 29#5 →
      Q (mkS sf (sv 30#5) r' (S + 176#64) m' sf.pstate))
    {sb : State} {r : BitVec 5 → BitVec 64} {m : Memory} {ps : PState}
    (hI : LInv mpl s0 R S O T X tb sv 8 sb r m) :
    Reach mpl 6 Q (mkS sb (mpl.base 6 + BitVec.ofNat 64 424) r S m ps) := by
  obtain ⟨hrun, hvr, hCL, hmi, hfx, hacc, h19, h20, h21, h22, h23, h24, -, -, h27, h28, h29⟩ := hI
  have hWs : ∀ a, InRegion O 120 a → InRegion S 176 a ∨ InRegion O 120 a := fun a h => Or.inr h
  rw [regL_init r, h19, h20, h21, h22, h23, h24, h27, h28, h29]
  refine pre2_run (hCL 6 (by decide)) hrun (mi_wowned hmi hWs) (memOK_refl m _) hsp (mi_rd1 hmi)
    (mi_rd2 hmi) (mi_rd3 hmi) hfx.1 ?_
  intro a8
  refine call_bb hP hrun hCL (f06_432 hP (hCL 6 (by decide))) hsp (mi_pre_call hmi) ?_
  intro sf hrunf hpcf hspf hkept hvrf hCLf hmemf hx0
  obtain ⟨hmif, hbytes⟩ := mi_call hmemf
  have k19 : sf.regs.regs 19#5 = selAcc tb (X.truncate 8) 8 12 := hkept 19#5 (by decide) (by decide)
  have k20 : sf.regs.regs 20#5 = selAcc tb (X.truncate 8) 8 11 := hkept 20#5 (by decide) (by decide)
  have k21 : sf.regs.regs 21#5 = selAcc tb (X.truncate 8) 8 0 := hkept 21#5 (by decide) (by decide)
  have k22 : sf.regs.regs 22#5 = selAcc tb (X.truncate 8) 8 6 := hkept 22#5 (by decide) (by decide)
  have k23 : sf.regs.regs 23#5 = selAcc tb (X.truncate 8) 8 5 := hkept 23#5 (by decide) (by decide)
  have k24 : sf.regs.regs 24#5 = selAcc tb (X.truncate 8) 8 10 := hkept 24#5 (by decide) (by decide)
  have k27 : sf.regs.regs 27#5 = selAcc tb (X.truncate 8) 8 14 := hkept 27#5 (by decide) (by decide)
  have k28 : sf.regs.regs 28#5 = selAcc tb (X.truncate 8) 8 13 := hkept 28#5 (by decide) (by decide)
  have k29 : sf.regs.regs 29#5 = S + 80#64 := hkept 29#5 (by decide) (by decide)
  have hq0 : sf.regs.regs 0#5 &&& 255#64 = if X.getLsbD 7 = true then 1#64 else 0#64 :=
    and255 (by rw [hx0]; rfl)
  obtain ⟨f4, f8, f16, f20, f80, f88, f96, f104, f112, f120, f128, f136, f144, f152, f160, f168⟩ :=
    fx_of_fixB (fixB_of_all hbytes) hfx
  obtain ⟨b1, b2, b3, b4, b7, b8, b9⟩ := acc_of_all hbytes hacc
  apply reach_of_sf hpcf hspf
  rw [k19, k20, k21, k22, k23, k24, k27, k28, k29]
  refine epi_run (hCLf 6 (by decide)) hrunf (mi_wowned hmif hWs) (memOK_refl _ _) hsp (mi_rd1 hmif)
    (mi_rd2 hmif) (mi_rd3 hmif) (wout1 O) (wout2 O)
    (stk_fact hmif 8 (by omega) (f8.trans hO)) (stk_fact hmif 24 (by omega) b2)
    (stk_fact hmif 32 (by omega) b1) (stk_fact hmif 40 (by omega) b7)
    (stk_fact hmif 48 (by omega) b4) (stk_fact hmif 56 (by omega) b3)
    (stk_fact hmif 64 (by omega) b8) (stk_fact hmif 72 (by omega) b9)
    (stk_fact hmif 80 (by omega) f80) (stk_fact hmif 88 (by omega) f88)
    (stk_fact hmif 96 (by omega) f96) (stk_fact hmif 104 (by omega) f104)
    (stk_fact hmif 112 (by omega) f112) (stk_fact hmif 120 (by omega) f120)
    (stk_fact hmif 128 (by omega) f128) (stk_fact hmif 136 (by omega) f136)
    (stk_fact hmif 144 (by omega) f144) (stk_fact hmif 152 (by omega) f152)
    (stk_fact hmif 160 (by omega) f160) (stk_fact hmif 168 (by omega) f168) hq0 ?_
  intro m' r' hok' o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29
  exact hQ sf m' r' hrunf (hvrf.trans hvr) (mi_frame hmif hok' hWs) o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29

end X25519Dalek.ESel
end

section
/-! # `LookupTable<AffineNielsPoint>::select` (block 6): the contract `fnOk` -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.ESel

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj

abbrev selName : String :=
  "<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::select"

theorem sel_lookup : lookupBlockSym selName x25519CliMultiLib.blocks = some (6, 0) := by
  decide +kernel

theorem ent_exists_pure {α : Type} {P : α → SepProp} {ψ : α → Prop} (x : α) (h : ψ x) :
    P x ⊢ ∃∗ y, P y ∗ ⌜ψ y⌝ := by
  intro k hk
  exact ⟨x, k, Heap.empty, disjoint_symm (disjoint_empty k), (union_empty k).symm, hk, rfl, h⟩

theorem trunc8_32 (v : BitVec 64) : BitVec.truncate 8 (BitVec.truncate 32 v) = v.truncate 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi] <;> omega

/-- The outcome at the return: registers, stack pointer, and the postcondition. -/
theorem outcome_final {mpl : MultiPlacement} {s0 sf : State} {R : SepProp} {S O T : BitVec 64}
    {x : BitVec 8} {ob tb : List (BitVec 8)} {m' : Memory} {r' : BitVec 5 → BitVec 64}
    (hS : S + 176#64 = s0.sp) (hrunf : sf.status = .Running)
    (hvr : calleeSavedVRegs sf = calleeSavedVRegs s0) (hmi : MI m' S O T tb R)
    {X : BitVec 64} (hX : X.truncate 8 = x) (htb : fe51LookupTable8Bounded tb (2 ^ 53))
    (o0 : m'.read64 O = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 5 else selAcc tb (X.truncate 8) 8 0))
    (o1 : m'.read64 (O + 8#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 6 else selAcc tb (X.truncate 8) 8 1))
    (o2 : m'.read64 (O + 16#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 7 else selAcc tb (X.truncate 8) 8 2))
    (o3 : m'.read64 (O + 24#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 8 else selAcc tb (X.truncate 8) 8 3))
    (o4 : m'.read64 (O + 32#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 9 else selAcc tb (X.truncate 8) 8 4))
    (o5 : m'.read64 (O + 40#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 0 else selAcc tb (X.truncate 8) 8 5))
    (o6 : m'.read64 (O + 48#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 1 else selAcc tb (X.truncate 8) 8 6))
    (o7 : m'.read64 (O + 56#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 2 else selAcc tb (X.truncate 8) 8 7))
    (o8 : m'.read64 (O + 64#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 3 else selAcc tb (X.truncate 8) 8 8))
    (o9 : m'.read64 (O + 72#64) = (if X.getLsbD 7 = true then selAcc tb (X.truncate 8) 8 4 else selAcc tb (X.truncate 8) 8 9))
    (o10 : m'.read64 (O + 80#64) = (if X.getLsbD 7 = true then nd0 (selAcc tb (X.truncate 8) 8 10) (selAcc tb (X.truncate 8) 8 14) else selAcc tb (X.truncate 8) 8 10))
    (o11 : m'.read64 (O + 88#64) = (if X.getLsbD 7 = true then nd1 (selAcc tb (X.truncate 8) 8 11) (selAcc tb (X.truncate 8) 8 10) else selAcc tb (X.truncate 8) 8 11))
    (o12 : m'.read64 (O + 96#64) = (if X.getLsbD 7 = true then ndk (selAcc tb (X.truncate 8) 8 12) (selAcc tb (X.truncate 8) 8 11) else selAcc tb (X.truncate 8) 8 12))
    (o13 : m'.read64 (O + 104#64) = (if X.getLsbD 7 = true then ndk (selAcc tb (X.truncate 8) 8 13) (selAcc tb (X.truncate 8) 8 12) else selAcc tb (X.truncate 8) 8 13))
    (o14 : m'.read64 (O + 112#64) = (if X.getLsbD 7 = true then ndk (selAcc tb (X.truncate 8) 8 14) (selAcc tb (X.truncate 8) 8 13) else selAcc tb (X.truncate 8) 8 14))
    (r19 : r' 19#5 = s0.regs.regs 19#5) (r20 : r' 20#5 = s0.regs.regs 20#5) (r21 : r' 21#5 = s0.regs.regs 21#5) (r22 : r' 22#5 = s0.regs.regs 22#5) (r23 : r' 23#5 = s0.regs.regs 23#5) (r24 : r' 24#5 = s0.regs.regs 24#5) (r25 : r' 25#5 = s0.regs.regs 25#5) (r26 : r' 26#5 = s0.regs.regs 26#5) (r27 : r' 27#5 = s0.regs.regs 27#5) (r28 : r' 28#5 = s0.regs.regs 28#5) (r29 : r' 29#5 = s0.regs.regs 29#5) :
    SubroutineOutcome (x25519CliMultiLib.withCodeLoaded mpl
      (ToBaseSpec.toSpec ((fun _ => lookupTableAffineNielsSelectSpec) mpl) (mpl.base 6)))
      (O, T, x, ob, tb) R s0 (mkS sf (s0.regs.regs 30#5) r' (S + 176#64) m' sf.pstate) := by
  refine Or.inl ⟨⟨?_, ?_, hrunf⟩, ⟨?_, ?_⟩, ?_⟩
  · simp [State.readReg64, RegFile.read, Reg.lr]
  · rw [mkS_sp, hS]
  · rw [mkS_sp, hS]
  · have e : ∀ k : BitVec 5, k ≠ 31#5 → r' k = s0.regs.regs k →
        (mkS sf (s0.regs.regs 30#5) r' (S + 176#64) m' sf.pstate).readReg64 (.gpr k) = s0.readReg64 (.gpr k) := by
      intro k hk hr
      rw [rd_gpr' _ _ _ _ _ _ _ hk, hr]
      simp [State.readReg64, RegFile.read, hk]
    exact ⟨e _ (by decide) r19, e _ (by decide) r20, e _ (by decide) r21, e _ (by decide) r22,
      e _ (by decide) r23, e _ (by decide) r24, e _ (by decide) r25, e _ (by decide) r26,
      e _ (by decide) r27, e _ (by decide) r28, e _ (by decide) r29, hvr⟩
  · rw [hX] at o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14
    have hc : x.msb = X.getLsbD 7 := by rw [msb_eq, hX]
    have lt := selAcc_lt x htb 8 le_rfl
    have hψ : (bytesAt m' O 120).length = 120 ∧ fe51AffineNielsBoundedAt (bytesAt m' O 120) 0 (2 ^ 53) ∧
        (fe51ValAt (bytesAt m' O 120) 0 % p25519, fe51ValAt (bytesAt m' O 120) 40 % p25519,
          fe51ValAt (bytesAt m' O 120) 80 % p25519) = edSelectAffineNiels tb x := by
      refine ⟨bytesAt_length _ _ _, final_post tb _ x _ hc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        ⟨lt 0 (by omega), lt 1 (by omega), lt 2 (by omega), lt 3 (by omega), lt 4 (by omega),
          lt 5 (by omega), lt 6 (by omega), lt 7 (by omega), lt 8 (by omega), lt 9 (by omega),
          lt 10 (by omega), lt 11 (by omega), lt 12 (by omega), lt 13 (by omega), lt 14 (by omega)⟩
        (sel_chain tb x) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
      · rw [readLE_bytesAt _ _ _ _ (by norm_num), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
        exact o0
      · rw [readLE_bytesAt _ _ _ _ (by norm_num)]; exact o1
      · rw [readLE_bytesAt _ _ _ _ (by norm_num)]; exact o2
      · rw [readLE_bytesAt _ _ _ _ (by norm_num)]; exact o3
      · rw [readLE_bytesAt _ _ _ _ (by norm_num)]; exact o4
      · rw [readLE_bytesAt _ _ _ _ (by norm_num)]; exact o5
      · rw [readLE_bytesAt _ _ _ _ (by norm_num)]; exact o6
      · rw [readLE_bytesAt _ _ _ _ (by norm_num)]; exact o7
      · rw [readLE_bytesAt _ _ _ _ (by norm_num)]; exact o8
      · rw [readLE_bytesAt _ _ _ _ (by norm_num)]; exact o9
      · rw [readLE_bytesAt _ _ _ _ (by norm_num)]; exact o10
      · rw [readLE_bytesAt _ _ _ _ (by norm_num)]; exact o11
      · rw [readLE_bytesAt _ _ _ _ (by norm_num)]; exact o12
      · rw [readLE_bytesAt _ _ _ _ (by norm_num)]; exact o13
      · rw [readLE_bytesAt _ _ _ _ (by norm_num)]; exact o14
    have hreg : S + 176#64 - BitVec.ofNat 64 192 = S - 16#64 := by bv_omega
    have hmerge := region_merge (S - 16#64) 16 176 (by norm_num)
    rw [BitVec.sub_add_cancel] at hmerge
    simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, lookupTableAffineNielsSelectSpec,
      stackFrame, mkS_sp, hreg]
    refine sat_mono_left hmi fun h hh => ?_
    rw [← sepConj_assoc] at hh
    have hh2 := sep_mono (fun h1 p1 => hmerge h1 (sep_mono (fun _ p => p) (bytes_memRegion S _) h1 p1))
      (sep_mono (ent_exists_pure (P := fun res => O ↦ₛ res) (ψ := fun res => res.length = 120 ∧
        fe51AffineNielsBoundedAt res 0 (2 ^ 53) ∧ (fe51ValAt res 0 % p25519, fe51ValAt res 40 % p25519,
          fe51ValAt res 80 % p25519) = edSelectAffineNiels tb x) _ hψ) (fun _ p => p)) h hh
    rw [show (16 : Nat) + 176 = 192 from rfl] at hh2
    rw [sepConj_comm _ (T ↦ᵣ tb), sepConj_left_comm] at hh2
    exact hh2

theorem insub (S a : BitVec 64) (h : InRegion S 176 a) : InRegion (S - 16#64) 192 a := by
  unfold InRegion at h ⊢
  rw [show a - (S - 16#64) = (a - S) + 16#64 by abel]
  bv_omega

theorem select_ok : fnOk selName (fun _ => lookupTableAffineNielsSelectSpec) := by
  refine ⟨6, 0, sel_lookup, fun mpl hP => ?_⟩
  rintro ⟨O, T, x, ob, tb⟩ R s0 hpc hrun hpre hal hCLp
  have hfa : x25519CliMultiLib.fnAddr mpl selName = mpl.base 6 + BitVec.ofNat 64 0 := by
    simp only [MultiPlacedLib.fnAddr, sel_lookup]
  rw [hfa] at hpc
  change s0.mem ⊨ ((⌜s0.readReg64 Reg.x0 = O ∧ s0.readReg64 Reg.x1 = T ∧
      BitVec.truncate 8 (s0.readReg32 Reg.x2) = x ∧ ob.length = 120 ∧
      fe51LookupTable8Bounded tb (2 ^ 53)⌝ ∗
      ((T ↦ᵣ tb) ∗ ((O ↦ₛ ob) ∗ memRegion (s0.sp - BitVec.ofNat 64 192) 192))) ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝) ∗ R at hpre
  rw [sepConj_comm (_ ∗ _) ⌜_⌝, sepConj_assoc, sat_pure_sep_iff, sepConj_assoc, sat_pure_sep_iff] at hpre
  obtain ⟨hCL, ⟨hx0, hx1, hx2, hol, htb⟩, hpre⟩ := hpre
  have hO : s0.regs.regs 0#5 = O := by simpa [State.readReg64, RegFile.read] using hx0
  have hT : s0.regs.regs 1#5 = T := by simpa [State.readReg64, RegFile.read] using hx1
  have hX : (s0.regs.regs 2#5).truncate 8 = x := by
    rw [← hx2, State.readReg32, trunc8_32]; simp [State.readReg64, RegFile.read, Reg.x2]
  have htl : tb.length = 960 := htb.1
  have hsp0 : s0.sp.toNat % 16 = 0 := (spAligned_iff s0).1 hal
  have hsp : (s0.sp - 176#64).toNat % 16 = 0 := sp_sub_aligned hsp0 176 rfl (by decide)
  have hreg : s0.sp - BitVec.ofNat 64 192 = s0.sp - 176#64 - 16#64 := by bv_omega
  rw [hreg] at hpre
  generalize hSd : s0.sp - 176#64 = S at hsp hpre
  have hS : S + 176#64 = s0.sp := by rw [← hSd, BitVec.sub_add_cancel]
  have hW : WOwned s0.mem (InRegion S 176) :=
    wowned_of hpre (ownsRW_sep_right (ownsRW_sep_right
      (ownsRW_mono (ownsRW_region (S - 16#64) 192) (fun a h => insub S a h))))
  show Reach mpl 6 _ s0
  apply reach_start
  rw [hpc, regL_init s0.regs.regs, ← hS]
  refine pro_run (hCL 6 (by decide)) hrun hW hsp (wstk1 S) (wstk2 S) (wstk3 S) ?_
  intro r' m' hok' hfx hacc g19 g20 g21 g22 g23 g24 g25 g26 g27 g28 g29
  have hsplit : Rf m' (memRegion (S - 16#64) 192) (memRegion (S - 16#64) 16 ∗ (S ↦ₛ bytesAt m' S 176)) := by
    have := rf_region_split m' (S - 16#64) 16 176 (by norm_num)
    rw [BitVec.sub_add_cancel] at this
    exact this
  have hbo := rf_bytes m' ob O
  rw [hol] at hbo
  have hmi : MI m' S O T tb R := by
    refine frame hpre hok' (ownsRW_sep_right (ownsRW_sep_right
      (ownsRW_mono (ownsRW_region (S - 16#64) 192) (fun a h => insub S a h))))
      (rf_mono (rf_sep (rf_ro m' tb T) (rf_sep hbo hsplit)) (ent_of_eq ?_))
    simp only [sepConj_assoc, sepConj_comm, sepConj_left_comm]
  refine loop_all hP hsp htl (X := s0.regs.regs 2#5) (sv := s0.regs.regs)
    (fun sb r m ps hI => epi_from hP hsp hO (fun sf m' r' hrunf hvr hmi o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 =>
      outcome_final hS hrunf hvr hmi hX htb o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29) hI)
    7 0 (by norm_num) s0 r' m' s0.pstate
    ⟨hrun, rfl, libcl_memOK hW hok' hCL, hmi, hfx, hacc, g19, g20, g21, g22, g23, g24, ?_, g26,
      g27, g28, g29⟩
  rw [g25, hT]

end X25519Dalek.ESel
end

open X25519Dalek in
theorem solution :
    fnOk
      "<curve25519_dalek::window::LookupTable<curve25519_dalek::backend::serial::curve_models::AffineNielsPoint>>::select"
      (fun _ => lookupTableAffineNielsSelectSpec) :=
  X25519Dalek.ESel.select_ok
