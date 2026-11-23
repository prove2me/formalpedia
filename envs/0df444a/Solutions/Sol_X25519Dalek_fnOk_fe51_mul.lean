-- Prove2me | solution 1 for X25519Dalek.fnOk_fe51_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T10:26:48.65712+00:00
-- url     : https://prove2.me/submissions/1537d64f-9a24-46d5-ab08-28298978fd02

import Mathlib.Tactic.IntervalCases
import Definitions.Def_X25519Dalek_Spec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
/-! # Instruction fetch for the hook-free x25519-dalek blocks, abstract states, Reach

Fetch lemmas follow the zlib CRC-32 proofs (`ZlibCrc32.Small.Machine`), generalised to a block of
the multi-block library `x25519CliMultiLib`. -/

namespace X25519Dalek.Field

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
  interval_cases j <;> simp

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

end X25519Dalek.Field
end

section
/-! # Abstract states, reachability and one lemma per instruction shape -/

namespace X25519Dalek.Field

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

end X25519Dalek.Field
end

section
/-! # Memory: reads over writes, and the invariant that only owned writable bytes change -/

namespace X25519Dalek.Field

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

theorem canRead_of_W {m0 m : Memory} {W : BitVec 64 → Prop} (hW : WOwned m0 W) (h : MemOK m0 W m)
    {a : BitVec 64} {n : Nat} (ha : AllB W a n) : m.canRead a n = true :=
  canRead_of h fun j hj => by
    show (m0.perm _).r = true ∧ _
    rw [(hW _ (ha j hj)).1, (hW _ (ha j hj)).2]; exact ⟨rfl, rfl⟩

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
  interval_cases i <;> simp

theorem read64_write64_same (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    (m.write64 a v).read64 a = v := by
  have e := read8_write64_off m a
  unfold Memory.read64
  simp only []
  rw [show a + 0#64 = a + 0#64 from rfl, e, e, e, e, e, e, e, e]
  simpa using concat_bytes64 v

end X25519Dalek.Field
end

section
/-! # Heaps: refreshing the read-write cells after stores, and the frame rule -/

namespace X25519Dalek.Field

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

theorem refresh_empty (m : Memory) : refresh m Heap.empty = Heap.empty := rfl

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

end X25519Dalek.Field
end

section
/-! # The frame rule for straight-line stores, and points-to facts -/

namespace X25519Dalek.Field

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

theorem rf_pure' {m : Memory} {φ ψ : Prop} (h : φ → ψ) : Rf m ⌜φ⌝ ⌜ψ⌝ := by
  rintro h ⟨rfl, hφ⟩
  exact ⟨refresh_empty m, h hφ⟩

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

/-- In `A ∗ Q`, a byte held by every heap of `A` is not owned read-write by `Q`. -/
theorem not_W_of {A Q : SepProp} {W : BitVec 64 → Prop} {h : Heap} (hs : (A ∗ Q).holds h)
    (hQ : OwnsRW Q W) {x : BitVec 64} (hA : ∀ h1, A.holds h1 → h1.phys x ≠ none) : ¬ W x := by
  intro hw
  obtain ⟨h1, h2, hd, rfl, a, q⟩ := hs
  obtain ⟨b, hb⟩ := hQ h2 q x hw
  rcases hd.1 x with e | e | ⟨b', e1, e2⟩
  · exact hA h1 a e
  · rw [e] at hb; cases hb
  · rw [e2] at hb; cases hb

end X25519Dalek.Field
end

section
/-! # Execution of each instruction shape on an abstract state -/

namespace X25519Dalek.Field

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

theorem evalAddSub_adds (x y : BitVec 64) :
    evalAddSub .W64 .ADDS x y none = (x + y, some (AddWithCarry64 x y false).2) := by
  simp only [evalAddSub]
  rw [← awc_add]; rfl

theorem evalAddSub_adc (x y : BitVec 64) (c : Bool) :
    evalAddSub .W64 .ADD x y (some c) = ((AddWithCarry64 x y c).1, none) := by
  simp only [evalAddSub]; rfl

/-- `SUB SP, SP, #imm`. -/
theorem ex_subsp (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .SUB .sp .sp imm false) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) r (sp - imm.zeroExtend 64) m ps := by
  simp only [execInstWithSvc, execAddSubImm, State.readReg, rd_sp, Bool.false_eq_true, if_false,
    evalAddSub_sub, State.writeReg, wr_sp, mkS_advancePC]

/-- `ADD SP, SP, #imm`. -/
theorem ex_addsp (imm : BitVec 12) :
    execInstWithSvc svc (.addSubImm .W64 .ADD .sp .sp imm false) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) r (sp + imm.zeroExtend 64) m ps := by
  simp only [execInstWithSvc, execAddSubImm, State.readReg, rd_sp, Bool.false_eq_true, if_false,
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

/-- `MUL Xd, Xn, Xm` (`MADD` with `XZR`). -/
theorem ex_mul {d n k : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.dataProc3 .W64 .MADD (.gpr d) (.gpr n) (.gpr k) .xzr) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (r n * r k)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk, rd_xzr,
    BitVec.zero_add, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

/-- `MADD Xd, Xn, Xm, Xa`. -/
theorem ex_madd {d n k a : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5)
    (ha : a ≠ 31#5) :
    execInstWithSvc svc (.dataProc3 .W64 .MADD (.gpr d) (.gpr n) (.gpr k) (.gpr a)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (r a + r n * r k)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk,
    rd_gpr' _ _ _ _ _ _ _ ha, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

/-- The high 64 bits of the 128-bit product. -/
abbrev mulhi (x y : BitVec 64) : BitVec 64 := ((x.zeroExtend 128 * y.zeroExtend 128) >>> 64).truncate 64

/-- `UMULH Xd, Xn, Xm`. -/
theorem ex_umulh {d n k : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.dataProc3 .W64 .UMULH (.gpr d) (.gpr n) (.gpr k) .xzr) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (mulhi (r n) (r k))) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk,
    wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

/-- `ADDS Xd, Xn, Xm`. -/
theorem ex_adds {d n k : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .ADDS (.gpr d) (.gpr n) (.gpr k) .LSL 0) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (r n + r k)) sp m
        (AddWithCarry64 (r n) (r k) false).2 := by
  simp only [execInstWithSvc, execAddSubShift, State.writeReg, State.readReg,
    rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk, shiftVal, shift64, evalAddSub_adds,
    wr_gpr _ _ _ _ _ _ _ _ hd, mkS_setPState, mkS_advancePC]
  simp

/-- `ADD Xd, Xn, Xm, LSR #a`. -/
theorem ex_add_lsr {d n k : BitVec 5} {a : Nat} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .ADD (.gpr d) (.gpr n) (.gpr k) .LSR a) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (r n + (r k >>> (a % 64)))) sp m ps := by
  simp only [execInstWithSvc, execAddSubShift, State.writeReg, State.readReg,
    rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk, shiftVal, shift64, evalAddSub_add,
    wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

/-- `ADC Xd, Xn, Xm`. -/
theorem ex_adc {d n k : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubCarry .W64 .ADD (.gpr d) (.gpr n) (.gpr k)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (AddWithCarry64 (r n) (r k) ps.c).1) sp m ps := by
  simp only [execInstWithSvc, execAddSubCarry, State.writeReg, State.readReg,
    rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk, mkS_pstate, evalAddSub_adc,
    wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

/-- `EXTR Xd, Xn, Xm, #lsb`. -/
theorem ex_extr {d n k : BitVec 5} {lsb : Nat} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.extr .W64 (.gpr d) (.gpr n) (.gpr k) lsb) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (((r n ++ r k) >>> (lsb % 64)).truncate 64)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk,
    wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

/-- `AND Xd, Xn, #mask`. -/
theorem ex_andi {d n : BitVec 5} {mask : BitVec 64} (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.logicalImm .W64 .AND (.gpr d) (.gpr n) mask) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (r n &&& mask)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg, rd_gpr' _ _ _ _ _ _ _ hn, evalLogical,
    wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

/-- `CINC Xd, Xn, CS` (`CSINC Xd, Xn, Xn, CC`). -/
theorem ex_cinc {d n : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.condSelect .W64 .CSINC (.gpr d) (.gpr n) (.gpr n) .CC) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (if ps.c then r n + 1#64 else r n)) sp m ps := by
  show ((mkS s pc r sp m ps).writeReg .W64 (.gpr d) _).advancePC = _
  simp only [State.writeReg, State.readReg, rd_gpr' _ _ _ _ _ _ _ hn, ConditionHolds, mkS_pstate,
    wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]
  cases ps.c <;> rfl

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

end X25519Dalek.Field
end

section
/-! # Running a block: one step at a time from an abstract state; the outcome at `RET` -/

namespace X25519Dalek.Field

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

theorem sepConj_pure_true (P : SepProp) : (P ∗ ⌜True⌝) = P := by
  apply SepProp.ext; funext h
  apply propext
  constructor
  · rintro ⟨h1, h2, hd, rfl, p, rfl, -⟩
    rwa [union_empty]
  · intro p
    exact ⟨h, Heap.empty, disjoint_symm (disjoint_empty h), (union_empty h).symm, p, rfl, trivial⟩

theorem pure_of_sat {φ : Prop} {P R : SepProp} {m : Memory} (hs : m ⊨ (⌜φ⌝ ∗ P) ∗ R) : φ := by
  obtain ⟨_, ⟨h1, h2, _, rfl, ⟨h11, h12, _, rfl, ⟨_, hφ⟩, _⟩, _⟩, _⟩ := hs
  exact hφ

/-- The outcome of a block that returns to `x30` with the stack pointer and the callee-saved
registers restored. -/
theorem outcome_of {α : Type} {spec : Spec α} {x : α} {R : SepProp} {s0 : State}
    {r : BitVec 5 → BitVec 64} {m : Memory} {ps : PState}
    (hrun : s0.status = .Running)
    (hr : ∀ k : BitVec 5, 19 ≤ k.toNat → r k = s0.regs.regs k)
    (hpost : m ⊨ spec.post x s0 (mkS s0 (s0.regs.regs 30#5) r s0.sp m ps) ∗ R) :
    SubroutineOutcome spec x R s0 (mkS s0 (s0.regs.regs 30#5) r s0.sp m ps) := by
  refine Or.inl ⟨⟨?_, rfl, hrun⟩, ⟨rfl, ?_⟩, hpost⟩
  · simp [State.readReg64, RegFile.read]
  · have e : ∀ k : BitVec 5, 19 ≤ k.toNat → k ≠ 31#5 →
        (mkS s0 (s0.regs.regs 30#5) r s0.sp m ps).readReg64 (.gpr k) = s0.readReg64 (.gpr k) := by
      intro k hk1 hk2
      rw [rd_gpr, if_neg hk2, hr k hk1]
      simp [State.readReg64, RegFile.read, hk2]
    exact ⟨e 19#5 (by decide) (by decide), e 20#5 (by decide) (by decide),
      e 21#5 (by decide) (by decide), e 22#5 (by decide) (by decide),
      e 23#5 (by decide) (by decide), e 24#5 (by decide) (by decide),
      e 25#5 (by decide) (by decide), e 26#5 (by decide) (by decide),
      e 27#5 (by decide) (by decide), e 28#5 (by decide) (by decide),
      e 29#5 (by decide) (by decide), rfl⟩

end X25519Dalek.Field
end

section
/-! # Straight-line execution in SSA form

Each lemma executes one instruction from an abstract state `mkS s (pcb + n) r sp m ps` and hands
the continuation a fresh name for the value written, with its defining equation. The register
file is kept as a literal list (`regL`), so that reads and writes normalise by `simp`. -/

namespace X25519Dalek.Field

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

theorem r_mul {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.dataProc3 .W64 .MADD (.gpr d) (.gpr a) (.gpr b) .xzr))
    (h : ∀ t, t = r a * r b →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_mul hd ha hb, pc_add4]; exact h _ rfl)

theorem r_madd {d a b c : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hc : c ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.dataProc3 .W64 .MADD (.gpr d) (.gpr a) (.gpr b) (.gpr c)))
    (h : ∀ t, t = r c + r a * r b →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_madd hd ha hb hc, pc_add4]; exact h _ rfl)

theorem r_umulh {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.dataProc3 .W64 .UMULH (.gpr d) (.gpr a) (.gpr b) .xzr))
    (h : ∀ t, t = mulhi (r a) (r b) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_umulh hd ha hb, pc_add4]; exact h _ rfl)

theorem r_adds {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.addSubShift .W64 .ADDS (.gpr d) (.gpr a) (.gpr b) .LSL 0))
    (h : ∀ t, t = r a + r b →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m
        (AddWithCarry64 (r a) (r b) false).2)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_adds hd ha hb, pc_add4]; exact h _ rfl)

theorem r_add_lsr {d a b : BitVec 5} {k : Nat} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.addSubShift .W64 .ADD (.gpr d) (.gpr a) (.gpr b) .LSR k))
    (h : ∀ t, t = r a + (r b >>> (k % 64)) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_add_lsr hd ha hb, pc_add4]; exact h _ rfl)

theorem r_adc {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.addSubCarry .W64 .ADD (.gpr d) (.gpr a) (.gpr b)))
    (h : ∀ t, t = (AddWithCarry64 (r a) (r b) ps.c).1 →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_adc hd ha hb, pc_add4]; exact h _ rfl)

theorem r_extr {d a b : BitVec 5} {k : Nat} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.extr .W64 (.gpr d) (.gpr a) (.gpr b) k))
    (h : ∀ t, t = ((r a ++ r b) >>> (k % 64)).truncate 64 →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_extr hd ha hb, pc_add4]; exact h _ rfl)

theorem r_andi {d a : BitVec 5} {mask : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.logicalImm .W64 .AND (.gpr d) (.gpr a) mask))
    (h : ∀ t, t = r a &&& mask →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_andi hd ha, pc_add4]; exact h _ rfl)

theorem r_cinc {d a : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.condSelect .W64 .CSINC (.gpr d) (.gpr a) (.gpr a) .CC))
    (h : ∀ t, t = (if ps.c then r a + 1#64 else r a) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_cinc hd ha, pc_add4]; exact h _ rfl)

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

theorem regL_callee (L : List (BitVec 64)) (r : BitVec 5 → BitVec 64)
    (h : ∀ j, 19 ≤ j → j < 32 → L.getD j 0 = r (BitVec.ofNat 5 j)) :
    ∀ k : BitVec 5, 19 ≤ k.toNat → regL L k = r k := by
  intro k hk
  have := h k.toNat hk k.isLt
  simp only [regL]; rw [this]; simp

end X25519Dalek.Field
end

section
/-! # Natural-number meaning of the 64-bit operations used by the field blocks

The column and carry arithmetic follows DeepMind's `Shared51/Field51.lean`
(google-deepmind/code-verification @ 8c8d371f): each 64-bit operation is read as a statement
about `toNat`, and each column sum of 128-bit products is assembled by `omega`. -/

namespace X25519Dalek.Field

set_option maxRecDepth 100000

open Arm64

theorem awc1 (x y : BitVec 64) (c : Bool) :
    (AddWithCarry64 x y c).1.toNat = (x.toNat + y.toNat + (if c then 1 else 0)) % 2 ^ 64 := by
  simp only [AddWithCarry64]
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_add]
  have hx := x.isLt; have hy := y.isLt
  cases c <;> simp <;> omega

theorem awc_c (x y : BitVec 64) :
    (AddWithCarry64 x y false).2.c = decide (2 ^ 64 ≤ x.toNat + y.toNat) := by
  simp only [AddWithCarry64, Bool.false_eq_true, if_false]
  rw [BitVec.msb_eq_decide]
  congr 1
  apply propext
  rw [BitVec.toNat_add, BitVec.toNat_add]
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.toNat_ofNat, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]
  constructor <;> intro h <;> omega

theorem carry_nat (x y : BitVec 64) :
    (if (AddWithCarry64 x y false).2.c = true then 1 else 0) = (x.toNat + y.toNat) / 2 ^ 64 := by
  rw [awc_c]
  have hx := x.isLt; have hy := y.isLt
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat
  · simp only [h, decide_true, if_true]; omega
  · simp only [h, decide_false, Bool.false_eq_true, if_false]; omega

theorem tn_mul {v x y : BitVec 64} (h : v = x * y) : v.toNat = x.toNat * y.toNat % 2 ^ 64 := by
  subst h; exact BitVec.toNat_mul x y

theorem tn_mulhi {v x y : BitVec 64} (h : v = mulhi x y) :
    v.toNat = x.toNat * y.toNat / 2 ^ 64 := by
  subst h
  simp only [mulhi, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_mul]
  have hx := x.isLt; have hy := y.isLt
  have hxy : x.toNat * y.toNat < 2 ^ 128 := by
    calc x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
      _ = 2 ^ 128 := by norm_num
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 128), Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 128),
    Nat.mod_eq_of_lt hxy]
  omega

theorem tn_add {v x y : BitVec 64} (h : v = x + y) : v.toNat = (x.toNat + y.toNat) % 2 ^ 64 := by
  subst h; exact BitVec.toNat_add x y

theorem tn_adc {v x y u w : BitVec 64} (h : v = (AddWithCarry64 x y (AddWithCarry64 u w false).2.c).1) :
    v.toNat = (x.toNat + y.toNat + (u.toNat + w.toNat) / 2 ^ 64) % 2 ^ 64 := by
  subst h; rw [awc1, carry_nat]

theorem tn_cinc {v x u w : BitVec 64}
    (h : v = if (AddWithCarry64 u w false).2.c = true then x + 1#64 else x) :
    v.toNat = (x.toNat + (u.toNat + w.toNat) / 2 ^ 64) % 2 ^ 64 := by
  subst h
  rw [← carry_nat]
  have hx := x.isLt
  split
  · rw [BitVec.toNat_add]; simp
  · simp; omega

theorem tn_extr {v x y : BitVec 64} (h : v = BitVec.truncate 64 ((x ++ y) >>> 51)) :
    v.toNat = (x.toNat * 2 ^ 64 + y.toNat) / 2 ^ 51 % 2 ^ 64 := by
  subst h
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_append]
  have hy := y.isLt
  congr 2
  rw [← Nat.shiftLeft_add_eq_or_of_lt hy, Nat.shiftLeft_eq]

theorem tn_mask {v x : BitVec 64} (h : v = x &&& 2251799813685247#64) : v.toNat = x.toNat % 2 ^ 51 := by
  subst h
  rw [BitVec.toNat_and, show (2251799813685247#64 : BitVec 64).toNat = 2 ^ 51 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem tn_madd19 {v x y : BitVec 64} (h : v = x + y * 19#64) :
    v.toNat = (x.toNat + y.toNat * 19) % 2 ^ 64 := by
  subst h; rw [BitVec.toNat_add, BitVec.toNat_mul]; simp

theorem tn_lsr {v x y : BitVec 64} (h : v = x + y >>> 51) :
    v.toNat = (x.toNat + y.toNat / 2 ^ 51) % 2 ^ 64 := by
  subst h; rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem tn_mul19 {v x : BitVec 64} (h : v = x * 19#64) (hx : x.toNat < 2 ^ 54) :
    v.toNat = x.toNat * 19 := by
  subst h; rw [BitVec.toNat_mul]; simp; omega

/-- One accumulation step of a 128-bit sum `H·2⁶⁴ + L` by a 128-bit addend `dH·2⁶⁴ + dL`. -/
theorem acc_step {H L dH dL S D : Nat} (hS : H * 2 ^ 64 + L = S) (hD : dH * 2 ^ 64 + dL = D)
    (hL : L < 2 ^ 64) (hdL : dL < 2 ^ 64) (hlt : S + D < 2 ^ 128) :
    ((H + dH + (L + dL) / 2 ^ 64) % 2 ^ 64) * 2 ^ 64 + (L + dL) % 2 ^ 64 = S + D := by
  have hdm := Nat.div_add_mod (L + dL) (2 ^ 64)
  have key : (H + dH + (L + dL) / 2 ^ 64) * 2 ^ 64 + (L + dL) % 2 ^ 64 = S + D := by
    rw [← hS, ← hD]; linarith
  have hX : H + dH + (L + dL) / 2 ^ 64 < 2 ^ 64 := by
    apply Nat.lt_of_mul_lt_mul_right (a := 2 ^ 64)
    calc (H + dH + (L + dL) / 2 ^ 64) * 2 ^ 64
        ≤ (H + dH + (L + dL) / 2 ^ 64) * 2 ^ 64 + (L + dL) % 2 ^ 64 := Nat.le_add_right _ _
      _ = S + D := key
      _ < 2 ^ 128 := hlt
      _ = 2 ^ 64 * 2 ^ 64 := by norm_num
  rw [Nat.mod_eq_of_lt hX]; exact key

theorem prod_split (p : Nat) : p / 2 ^ 64 * 2 ^ 64 + p % 2 ^ 64 = p := by
  have := Nat.div_add_mod p (2 ^ 64); rw [Nat.mul_comm] at this; exact this

end X25519Dalek.Field
end

section
/-! # Limb arithmetic of `FieldElement51` multiplication

`fe51_mul_carry_nat`, `expand5_mul`, `mul_expand5` and `fe51_mul_poly_nat` are copied from
DeepMind's `Shared51/Field51.lean` (google-deepmind/code-verification @ 8c8d371f, Apache-2.0),
which proves the same block; the column lemmas restate their `add128_*` steps for the
operand order of the SSA run. -/

namespace X25519Dalek.Field

set_option maxRecDepth 20000

open Arm64

theorem prod_hl {vh vl x y : BitVec 64} (e1 : vh = mulhi x y) (e2 : vl = x * y) :
    vh.toNat * 2 ^ 64 + vl.toNat = x.toNat * y.toNat := by
  rw [tn_mulhi e1, tn_mul e2]; exact prod_split _

theorem col_step {H L dH dL H' L' : BitVec 64} {S D : Nat}
    (hS : H.toNat * 2 ^ 64 + L.toNat = S) (hD : dH.toNat * 2 ^ 64 + dL.toNat = D)
    (eL : L' = L + dL) (eH : H' = (AddWithCarry64 H dH (AddWithCarry64 L dL false).2.c).1)
    (hlt : S + D < 2 ^ 128) : H'.toNat * 2 ^ 64 + L'.toNat = S + D := by
  rw [tn_adc eH, tn_add eL]
  exact acc_step hS hD L.isLt dL.isLt hlt

theorem col_cinc {H L c H' L' : BitVec 64} {S : Nat}
    (hS : H.toNat * 2 ^ 64 + L.toNat = S)
    (eL : L' = L + c) (eH : H' = if (AddWithCarry64 L c false).2.c = true then H + 1#64 else H)
    (hlt : S + c.toNat < 2 ^ 128) : H'.toNat * 2 ^ 64 + L'.toNat = S + c.toNat := by
  rw [tn_cinc eH, tn_add eL]
  have := acc_step (H := H.toNat) (L := L.toNat) (dH := 0) (dL := c.toNat) (D := c.toNat) hS (by simp) L.isLt c.isLt
    (by simpa using hlt)
  simpa using this

theorem col_extract {H L c l : BitVec 64} {S : Nat}
    (hS : H.toNat * 2 ^ 64 + L.toNat = S) (hlt : S < 2 ^ 115)
    (ec : c = BitVec.truncate 64 ((H ++ L) >>> 51)) (el : l = L &&& 2251799813685247#64) :
    l.toNat + c.toNat * 2 ^ 51 = S ∧ l.toNat < 2 ^ 51 := by
  rw [tn_extr ec, tn_mask el, hS]
  have h1 : S / 2 ^ 51 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h1]
  have hL := L.isLt
  constructor
  · have : L.toNat % 2 ^ 51 = S % 2 ^ 51 := by rw [← hS]; omega
    rw [this]; omega
  · omega

theorem nat_mul_lt_19_108 {x y : Nat} (hx : x < 2 ^ 54) (hy : y < 19 * 2 ^ 54) : x * y < 19 * 2 ^ 108 := by
  calc x * y < 2 ^ 54 * (19 * 2 ^ 54) := Nat.mul_lt_mul'' hx hy
    _ = 19 * 2 ^ 108 := by norm_num
theorem nat_mul_lt_108 {x y : Nat} (hx : x < 2 ^ 54) (hy : y < 2 ^ 54) : x * y < 2 ^ 108 := by
  calc x * y < 2 ^ 54 * 2 ^ 54 := Nat.mul_lt_mul'' hx hy
    _ = 2 ^ 108 := by norm_num

theorem fe51_mul_carry_nat (S0 S1 S2 S3 S4 l0 l1 r0 r1 r2 r3 r4 c0 c1 c2 c3 c4 d0 : Nat)
    (hS0 : S0 < 95 * 2 ^ 108) (hS1 : S1 < 95 * 2 ^ 108) (hS2 : S2 < 95 * 2 ^ 108) (hS3 : S3 < 95 * 2 ^ 108) (hS4 : S4 < 5 * 2 ^ 108)
    (h0 : l0 + c0 * 2 ^ 51 = S0 ∧ l0 < 2 ^ 51) (h1 : l1 + c1 * 2 ^ 51 = S1 + c0 ∧ l1 < 2 ^ 51)
    (h2 : r2 + c2 * 2 ^ 51 = S2 + c1 ∧ r2 < 2 ^ 51) (h3 : r3 + c3 * 2 ^ 51 = S3 + c2 ∧ r3 < 2 ^ 51)
    (h4 : r4 + c4 * 2 ^ 51 = S4 + c3 ∧ r4 < 2 ^ 51) (hd0 : r0 + d0 * 2 ^ 51 = l0 + c4 * 19 ∧ r0 < 2 ^ 51) (hr1 : r1 = l1 + d0) :
    r0 < 2 ^ 52 ∧ r1 < 2 ^ 52 ∧ r2 < 2 ^ 52 ∧ r3 < 2 ^ 52 ∧ r4 < 2 ^ 52 ∧
    (r0 + r1 * 2 ^ 51 + r2 * 2 ^ 102 + r3 * 2 ^ 153 + r4 * 2 ^ 204) + c4 * p25519 =
      S0 + S1 * 2 ^ 51 + S2 * 2 ^ 102 + S3 * 2 ^ 153 + S4 * 2 ^ 204 := by dsimp only [p25519]; omega

theorem expand5_mul (A0 A1 A2 A3 A4 B : Nat) :
    (A0 + A1 * 2 ^ 51 + A2 * 2 ^ 102 + A3 * 2 ^ 153 + A4 * 2 ^ 204) * B =
      A0 * B + A1 * B * 2 ^ 51 + A2 * B * 2 ^ 102 + A3 * B * 2 ^ 153 + A4 * B * 2 ^ 204 := by
  simp only [Nat.add_mul, Nat.mul_right_comm _ _ B]

theorem mul_expand5 (A B0 B1 B2 B3 B4 : Nat) :
    A * (B0 + B1 * 2 ^ 51 + B2 * 2 ^ 102 + B3 * 2 ^ 153 + B4 * 2 ^ 204) =
      A * B0 + A * B1 * 2 ^ 51 + A * B2 * 2 ^ 102 + A * B3 * 2 ^ 153 + A * B4 * 2 ^ 204 := by
  simp only [Nat.mul_add, ← Nat.mul_assoc]

theorem fe51_mul_poly_nat (A0 A1 A2 A3 A4 B0 B1 B2 B3 B4 : Nat) :
    ∃ K : Nat,
      ((A4 * (B1 * 19) + B0 * A0 + A3 * (B2 * 19) + A2 * (B3 * 19) + A1 * (B4 * 19)) +
       (A4 * (B2 * 19) + A0 * B1 + A3 * (B3 * 19) + A2 * (B4 * 19) + A1 * B0) * 2 ^ 51 +
       (A4 * (B3 * 19) + A0 * B2 + A3 * (B4 * 19) + A2 * B0 + A1 * B1) * 2 ^ 102 +
       (A4 * (B4 * 19) + A0 * B3 + A3 * B0 + A2 * B1 + A1 * B2) * 2 ^ 153 +
       (A4 * B0 + A0 * B4 + A3 * B1 + A2 * B2 + A1 * B3) * 2 ^ 204) + K * p25519 =
      (A0 + A1 * 2 ^ 51 + A2 * 2 ^ 102 + A3 * 2 ^ 153 + A4 * 2 ^ 204) *
      (B0 + B1 * 2 ^ 51 + B2 * 2 ^ 102 + B3 * 2 ^ 153 + B4 * 2 ^ 204) := by
  refine ⟨A4 * B1 + (A3 * B2 + A4 * B2 * 2 ^ 51) + (A2 * B3 + A3 * B3 * 2 ^ 51 + A4 * B3 * 2 ^ 102) +
    (A1 * B4 + A2 * B4 * 2 ^ 51 + A3 * B4 * 2 ^ 102 + A4 * B4 * 2 ^ 153), ?_⟩
  dsimp only [p25519]
  rw [mul_expand5, expand5_mul _ _ _ _ _ B0, expand5_mul _ _ _ _ _ B1,
      expand5_mul _ _ _ _ _ B2, expand5_mul _ _ _ _ _ B3, expand5_mul _ _ _ _ _ B4, Nat.mul_comm B0 A0]
  simp only [Nat.add_mul, ← Nat.mul_assoc]; omega


theorem col_stepB {H L dH dL H' L' : BitVec 64} {S D X Y : Nat}
    (hS : H.toNat * 2 ^ 64 + L.toNat = S) (hSb : S < X) (hD : dH.toNat * 2 ^ 64 + dL.toNat = D)
    (hDb : D < Y) (hXY : X + Y ≤ 2 ^ 128)
    (eL : L' = L + dL) (eH : H' = (AddWithCarry64 H dH (AddWithCarry64 L dL false).2.c).1) :
    H'.toNat * 2 ^ 64 + L'.toNat = S + D ∧ S + D < X + Y :=
  ⟨col_step hS hD eL eH (by omega), by omega⟩

theorem col_cincB {H L c H' L' : BitVec 64} {S X : Nat}
    (hS : H.toNat * 2 ^ 64 + L.toNat = S) (hSb : S < X) (hX : X + 2 ^ 64 ≤ 2 ^ 128)
    (eL : L' = L + c) (eH : H' = if (AddWithCarry64 L c false).2.c = true then H + 1#64 else H) :
    H'.toNat * 2 ^ 64 + L'.toNat = S + c.toNat ∧ S + c.toNat < X + 2 ^ 64 := by
  have := c.isLt
  exact ⟨col_cinc hS eL eH (by omega), by omega⟩

theorem col_extractB {H L c l : BitVec 64} {S X : Nat}
    (hS : H.toNat * 2 ^ 64 + L.toNat = S) (hSb : S < X) (hX : X ≤ 2 ^ 115)
    (ec : c = BitVec.truncate 64 ((H ++ L) >>> 51)) (el : l = L &&& 2251799813685247#64) :
    l.toNat + c.toNat * 2 ^ 51 = S ∧ l.toNat < 2 ^ 51 :=
  col_extract hS (by omega) ec el

theorem c4_bound {r c S c3 : Nat} (h : r + c * 2 ^ 51 = S + c3 ∧ r < 2 ^ 51) (hS : S < 5 * 2 ^ 108)
    (hc3 : c3 < 2 ^ 64) : c < 6 * 2 ^ 57 := by omega

theorem mul_final_carry {l0 l1 c4 v620 v628 v624 : BitVec 64} (hl0 : l0.toNat < 2 ^ 51)
    (hl1 : l1.toNat < 2 ^ 51) (hc4 : c4.toNat < 6 * 2 ^ 57) (e620 : v620 = l0 + c4 * 19#64)
    (e628 : v628 = v620 &&& 2251799813685247#64) (e624 : v624 = l1 + v620 >>> 51) :
    (v628.toNat + v620.toNat / 2 ^ 51 * 2 ^ 51 = l0.toNat + c4.toNat * 19 ∧ v628.toNat < 2 ^ 51) ∧
      v624.toNat = l1.toNat + v620.toNat / 2 ^ 51 := by
  have g : v620.toNat = l0.toNat + c4.toNat * 19 := by rw [tn_madd19 e620]; omega
  rw [tn_mask e628, tn_lsr e624, g]
  omega

theorem lt_of_lt_le' {a b c : Nat} (h : a < b) (h' : b ≤ c) : a < c := Nat.lt_of_lt_of_le h h'

theorem mul_arith {A0 A1 A2 A3 A4 B0 B1 B2 B3 B4 : BitVec 64}
    {v56 v60 v64 v68 v72 v76 v200 v244 v96 v124 v100 v164 v80 v92 v116 v128 v268 v256 v120 v144 v136 v108 v204 v168 v140 v156 v348 v284 v104 v160 v180 v184 v220 v248 v176 v192 v416 v400 v232 v148 v296 v324 v432 v476 v212 v228 v516 v496 v216 v236 v452 v464 v552 v532 v260 v272 v280 v288 v292 v300 v304 v312 v328 v332 v316 v336 v344 v356 v360 v368 v372 v380 v384 v392 v412 v420 v396 v404 v424 v436 v440 v444 v448 v460 v468 v472 v484 v636 v480 v488 v492 v500 v504 v508 v524 v536 v540 v544 v560 v640 v568 v572 v580 v584 v588 v592 v596 v600 v604 v612 v616 v648 v620 v628 v624 : BitVec 64}
    (e56 : v56 = B1 * 19#64)
    (e60 : v60 = B2 * 19#64)
    (e64 : v64 = B3 * 19#64)
    (e68 : v68 = B4 * 19#64)
    (e72 : v72 = mulhi A4 v56)
    (e76 : v76 = A4 * v56)
    (e200 : v200 = mulhi B0 A0)
    (e244 : v244 = B0 * A0)
    (e96 : v96 = mulhi A3 v60)
    (e124 : v124 = A3 * v60)
    (e100 : v100 = mulhi A2 v64)
    (e164 : v164 = A2 * v64)
    (e80 : v80 = mulhi A1 v68)
    (e92 : v92 = A1 * v68)
    (e116 : v116 = mulhi A4 v60)
    (e128 : v128 = A4 * v60)
    (e268 : v268 = mulhi A0 B1)
    (e256 : v256 = A0 * B1)
    (e120 : v120 = mulhi A3 v64)
    (e144 : v144 = A3 * v64)
    (e136 : v136 = mulhi A2 v68)
    (e108 : v108 = A2 * v68)
    (e204 : v204 = mulhi A1 B0)
    (e168 : v168 = A1 * B0)
    (e140 : v140 = mulhi A4 v64)
    (e156 : v156 = A4 * v64)
    (e348 : v348 = mulhi A0 B2)
    (e284 : v284 = A0 * B2)
    (e104 : v104 = mulhi A3 v68)
    (e160 : v160 = A3 * v68)
    (e180 : v180 = mulhi A2 B0)
    (e184 : v184 = A2 * B0)
    (e220 : v220 = mulhi A1 B1)
    (e248 : v248 = A1 * B1)
    (e176 : v176 = mulhi A4 v68)
    (e192 : v192 = A4 * v68)
    (e416 : v416 = mulhi A0 B3)
    (e400 : v400 = A0 * B3)
    (e232 : v232 = mulhi A3 B0)
    (e148 : v148 = A3 * B0)
    (e296 : v296 = mulhi A2 B1)
    (e324 : v324 = A2 * B1)
    (e432 : v432 = mulhi A1 B2)
    (e476 : v476 = A1 * B2)
    (e212 : v212 = mulhi A4 B0)
    (e228 : v228 = A4 * B0)
    (e516 : v516 = mulhi A0 B4)
    (e496 : v496 = A0 * B4)
    (e216 : v216 = mulhi A3 B1)
    (e236 : v236 = A3 * B1)
    (e452 : v452 = mulhi A2 B2)
    (e464 : v464 = A2 * B2)
    (e552 : v552 = mulhi A1 B3)
    (e532 : v532 = A1 * B3)
    (e260 : v260 = v76 + v244)
    (e272 : v272 = (AddWithCarry64 v72 v200 (AddWithCarry64 v76 v244 false).2.c).1)
    (e280 : v280 = v260 + v124)
    (e288 : v288 = (AddWithCarry64 v272 v96 (AddWithCarry64 v260 v124 false).2.c).1)
    (e292 : v292 = v280 + v164)
    (e300 : v300 = (AddWithCarry64 v288 v100 (AddWithCarry64 v280 v164 false).2.c).1)
    (e304 : v304 = v292 + v92)
    (e312 : v312 = (AddWithCarry64 v300 v80 (AddWithCarry64 v292 v92 false).2.c).1)
    (e328 : v328 = BitVec.truncate 64 ((v312 ++ v304) >>> 51))
    (e332 : v332 = v304 &&& 2251799813685247#64)
    (e316 : v316 = v128 + v256)
    (e336 : v336 = (AddWithCarry64 v116 v268 (AddWithCarry64 v128 v256 false).2.c).1)
    (e344 : v344 = v316 + v144)
    (e356 : v356 = (AddWithCarry64 v336 v120 (AddWithCarry64 v316 v144 false).2.c).1)
    (e360 : v360 = v344 + v108)
    (e368 : v368 = (AddWithCarry64 v356 v136 (AddWithCarry64 v344 v108 false).2.c).1)
    (e372 : v372 = v360 + v168)
    (e380 : v380 = (AddWithCarry64 v368 v204 (AddWithCarry64 v360 v168 false).2.c).1)
    (e384 : v384 = v372 + v328)
    (e392 : v392 = if (AddWithCarry64 v372 v328 false).2.c = true then v380 + 1#64 else v380)
    (e412 : v412 = BitVec.truncate 64 ((v392 ++ v384) >>> 51))
    (e420 : v420 = v384 &&& 2251799813685247#64)
    (e396 : v396 = v156 + v284)
    (e404 : v404 = (AddWithCarry64 v140 v348 (AddWithCarry64 v156 v284 false).2.c).1)
    (e424 : v424 = v396 + v160)
    (e436 : v436 = (AddWithCarry64 v404 v104 (AddWithCarry64 v396 v160 false).2.c).1)
    (e440 : v440 = v424 + v184)
    (e444 : v444 = (AddWithCarry64 v436 v180 (AddWithCarry64 v424 v184 false).2.c).1)
    (e448 : v448 = v440 + v248)
    (e460 : v460 = (AddWithCarry64 v444 v220 (AddWithCarry64 v440 v248 false).2.c).1)
    (e468 : v468 = v448 + v412)
    (e472 : v472 = if (AddWithCarry64 v448 v412 false).2.c = true then v460 + 1#64 else v460)
    (e484 : v484 = BitVec.truncate 64 ((v472 ++ v468) >>> 51))
    (e636 : v636 = v468 &&& 2251799813685247#64)
    (e480 : v480 = v192 + v400)
    (e488 : v488 = (AddWithCarry64 v176 v416 (AddWithCarry64 v192 v400 false).2.c).1)
    (e492 : v492 = v480 + v148)
    (e500 : v500 = (AddWithCarry64 v488 v232 (AddWithCarry64 v480 v148 false).2.c).1)
    (e504 : v504 = v492 + v324)
    (e508 : v508 = (AddWithCarry64 v500 v296 (AddWithCarry64 v492 v324 false).2.c).1)
    (e524 : v524 = v504 + v476)
    (e536 : v536 = (AddWithCarry64 v508 v432 (AddWithCarry64 v504 v476 false).2.c).1)
    (e540 : v540 = v524 + v484)
    (e544 : v544 = if (AddWithCarry64 v524 v484 false).2.c = true then v536 + 1#64 else v536)
    (e560 : v560 = BitVec.truncate 64 ((v544 ++ v540) >>> 51))
    (e640 : v640 = v540 &&& 2251799813685247#64)
    (e568 : v568 = v228 + v496)
    (e572 : v572 = (AddWithCarry64 v212 v516 (AddWithCarry64 v228 v496 false).2.c).1)
    (e580 : v580 = v568 + v236)
    (e584 : v584 = (AddWithCarry64 v572 v216 (AddWithCarry64 v568 v236 false).2.c).1)
    (e588 : v588 = v580 + v464)
    (e592 : v592 = (AddWithCarry64 v584 v452 (AddWithCarry64 v580 v464 false).2.c).1)
    (e596 : v596 = v588 + v532)
    (e600 : v600 = (AddWithCarry64 v592 v552 (AddWithCarry64 v588 v532 false).2.c).1)
    (e604 : v604 = v596 + v560)
    (e612 : v612 = if (AddWithCarry64 v596 v560 false).2.c = true then v600 + 1#64 else v600)
    (e616 : v616 = BitVec.truncate 64 ((v612 ++ v604) >>> 51))
    (e648 : v648 = v604 &&& 2251799813685247#64)
    (e620 : v620 = v332 + v616 * 19#64)
    (e628 : v628 = v620 &&& 2251799813685247#64)
    (e624 : v624 = v420 + v620 >>> 51)
    (hbA : A0.toNat < 2 ^ 54 ∧ A1.toNat < 2 ^ 54 ∧ A2.toNat < 2 ^ 54 ∧ A3.toNat < 2 ^ 54 ∧
      A4.toNat < 2 ^ 54)
    (hbB : B0.toNat < 2 ^ 54 ∧ B1.toNat < 2 ^ 54 ∧ B2.toNat < 2 ^ 54 ∧ B3.toNat < 2 ^ 54 ∧
      B4.toNat < 2 ^ 54) :
    v628.toNat < 2 ^ 52 ∧ v624.toNat < 2 ^ 52 ∧ v636.toNat < 2 ^ 52 ∧ v640.toNat < 2 ^ 52 ∧
      v648.toNat < 2 ^ 52 ∧
      fe51Val v628 v624 v636 v640 v648 % p25519 =
        fe51Val A0 A1 A2 A3 A4 * fe51Val B0 B1 B2 B3 B4 % p25519 := by
  obtain ⟨hA0b, hA1b, hA2b, hA3b, hA4b⟩ := hbA
  obtain ⟨hB0b, hB1b, hB2b, hB3b, hB4b⟩ := hbB
  have q1 := tn_mul19 e56 hB1b
  have q2 := tn_mul19 e60 hB2b
  have q3 := tn_mul19 e64 hB3b
  have q4 := tn_mul19 e68 hB4b
  -- products
  have p00 := prod_hl e72 e76
  have p01 := prod_hl e200 e244
  have p02 := prod_hl e96 e124
  have p03 := prod_hl e100 e164
  have p04 := prod_hl e80 e92
  have p10 := prod_hl e116 e128
  have p11 := prod_hl e268 e256
  have p12 := prod_hl e120 e144
  have p13 := prod_hl e136 e108
  have p14 := prod_hl e204 e168
  have p20 := prod_hl e140 e156
  have p21 := prod_hl e348 e284
  have p22 := prod_hl e104 e160
  have p23 := prod_hl e180 e184
  have p24 := prod_hl e220 e248
  have p30 := prod_hl e176 e192
  have p31 := prod_hl e416 e400
  have p32 := prod_hl e232 e148
  have p33 := prod_hl e296 e324
  have p34 := prod_hl e432 e476
  have p40 := prod_hl e212 e228
  have p41 := prod_hl e516 e496
  have p42 := prod_hl e216 e236
  have p43 := prod_hl e452 e464
  have p44 := prod_hl e552 e532
  rw [q1] at p00; rw [q2] at p02 p10; rw [q3] at p03 p12 p20; rw [q4] at p04 p13 p22 p30
  -- product bounds
  have b19 : ∀ {x y : BitVec 64}, x.toNat < 2 ^ 54 → y.toNat < 2 ^ 54 →
      x.toNat * (y.toNat * 19) < 19 * 2 ^ 108 := fun hx hy => nat_mul_lt_19_108 hx (by omega)
  have b1' : ∀ {x y : BitVec 64}, x.toNat < 2 ^ 54 → y.toNat < 2 ^ 54 →
      x.toNat * y.toNat < 19 * 2 ^ 108 := fun hx hy =>
        Nat.lt_of_lt_of_le (nat_mul_lt_108 hx hy) (by norm_num)
  have b1 : ∀ {x y : BitVec 64}, x.toNat < 2 ^ 54 → y.toNat < 2 ^ 54 →
      x.toNat * y.toNat < 2 ^ 108 := fun hx hy => nat_mul_lt_108 hx hy
  have k00 := b19 hA4b hB1b
  have k01 := b1' hB0b hA0b
  have k02 := b19 hA3b hB2b
  have k03 := b19 hA2b hB3b
  have k04 := b19 hA1b hB4b
  have k10 := b19 hA4b hB2b
  have k11 := b1' hA0b hB1b
  have k12 := b19 hA3b hB3b
  have k13 := b19 hA2b hB4b
  have k14 := b1' hA1b hB0b
  have k20 := b19 hA4b hB3b
  have k21 := b1' hA0b hB2b
  have k22 := b19 hA3b hB4b
  have k23 := b1' hA2b hB0b
  have k24 := b1' hA1b hB1b
  have k30 := b19 hA4b hB4b
  have k31 := b1' hA0b hB3b
  have k32 := b1' hA3b hB0b
  have k33 := b1' hA2b hB1b
  have k34 := b1' hA1b hB2b
  have k40 := b1 hA4b hB0b
  have k41 := b1 hA0b hB4b
  have k42 := b1 hA3b hB1b
  have k43 := b1 hA2b hB2b
  have k44 := b1 hA1b hB3b
  -- column 0
  obtain ⟨s01, t01⟩ := col_stepB p00 k00 p01 k01 (by norm_num) e260 e272
  obtain ⟨s02, t02⟩ := col_stepB s01 t01 p02 k02 (by norm_num) e280 e288
  obtain ⟨s03, t03⟩ := col_stepB s02 t02 p03 k03 (by norm_num) e292 e300
  obtain ⟨s04, t04⟩ := col_stepB s03 t03 p04 k04 (by norm_num) e304 e312
  have x0 := col_extractB s04 t04 (by norm_num) e328 e332
  -- column 1
  obtain ⟨s11, t11⟩ := col_stepB p10 k10 p11 k11 (by norm_num) e316 e336
  obtain ⟨s12, t12⟩ := col_stepB s11 t11 p12 k12 (by norm_num) e344 e356
  obtain ⟨s13, t13⟩ := col_stepB s12 t12 p13 k13 (by norm_num) e360 e368
  obtain ⟨s14, t14⟩ := col_stepB s13 t13 p14 k14 (by norm_num) e372 e380
  obtain ⟨s15, t15⟩ := col_cincB s14 t14 (by norm_num) e384 e392
  have x1 := col_extractB s15 t15 (by norm_num) e412 e420
  -- column 2
  obtain ⟨s21, t21⟩ := col_stepB p20 k20 p21 k21 (by norm_num) e396 e404
  obtain ⟨s22, t22⟩ := col_stepB s21 t21 p22 k22 (by norm_num) e424 e436
  obtain ⟨s23, t23⟩ := col_stepB s22 t22 p23 k23 (by norm_num) e440 e444
  obtain ⟨s24, t24⟩ := col_stepB s23 t23 p24 k24 (by norm_num) e448 e460
  obtain ⟨s25, t25⟩ := col_cincB s24 t24 (by norm_num) e468 e472
  have x2 := col_extractB s25 t25 (by norm_num) e484 e636
  -- column 3
  obtain ⟨s31, t31⟩ := col_stepB p30 k30 p31 k31 (by norm_num) e480 e488
  obtain ⟨s32, t32⟩ := col_stepB s31 t31 p32 k32 (by norm_num) e492 e500
  obtain ⟨s33, t33⟩ := col_stepB s32 t32 p33 k33 (by norm_num) e504 e508
  obtain ⟨s34, t34⟩ := col_stepB s33 t33 p34 k34 (by norm_num) e524 e536
  obtain ⟨s35, t35⟩ := col_cincB s34 t34 (by norm_num) e540 e544
  have x3 := col_extractB s35 t35 (by norm_num) e560 e640
  -- column 4
  obtain ⟨s41, t41⟩ := col_stepB p40 k40 p41 k41 (by norm_num) e568 e572
  obtain ⟨s42, t42⟩ := col_stepB s41 t41 p42 k42 (by norm_num) e580 e584
  obtain ⟨s43, t43⟩ := col_stepB s42 t42 p43 k43 (by norm_num) e588 e592
  obtain ⟨s44, t44⟩ := col_stepB s43 t43 p44 k44 (by norm_num) e596 e600
  obtain ⟨s45, t45⟩ := col_cincB s44 t44 (by norm_num) e604 e612
  have x4 := col_extractB s45 t45 (by norm_num) e616 e648
  have hc4 := c4_bound x4 (lt_of_lt_le' t44 (by norm_num)) v560.isLt
  obtain ⟨hd0, hr1⟩ := mul_final_carry x0.2 x1.2 hc4 e620 e628 e624
  obtain ⟨r0b, r1b, r2b, r3b, r4b, hcar⟩ := fe51_mul_carry_nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (lt_of_lt_le' t04 (by norm_num)) (lt_of_lt_le' t14 (by norm_num))
    (lt_of_lt_le' t24 (by norm_num)) (lt_of_lt_le' t34 (by norm_num))
    (lt_of_lt_le' t44 (by norm_num)) x0 x1 x2 x3 x4 hd0 hr1
  obtain ⟨K, hpoly⟩ := fe51_mul_poly_nat A0.toNat A1.toNat A2.toNat A3.toNat A4.toNat B0.toNat
    B1.toNat B2.toNat B3.toNat B4.toNat
  refine ⟨r0b, r1b, r2b, r3b, r4b, ?_⟩
  unfold fe51Val
  have htot : (v628.toNat + v624.toNat * 2 ^ 51 + v636.toNat * 2 ^ 102 + v640.toNat * 2 ^ 153 +
      v648.toNat * 2 ^ 204) + (v616.toNat + K) * p25519 =
      (A0.toNat + A1.toNat * 2 ^ 51 + A2.toNat * 2 ^ 102 + A3.toNat * 2 ^ 153 + A4.toNat * 2 ^ 204) *
      (B0.toNat + B1.toNat * 2 ^ 51 + B2.toNat * 2 ^ 102 + B3.toNat * 2 ^ 153 + B4.toNat * 2 ^ 204) := by
    rw [Nat.add_mul, ← Nat.add_assoc, hcar]; exact hpoly
  rw [← htot, Nat.add_mul_mod_self_right]

end X25519Dalek.Field
end

section
/-! # `<&FieldElement51 as Mul>::mul` (block 1, 166 instructions): the run -/

namespace X25519Dalek.Field

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Arm64 Arm64.Obj

theorem blk01 : x25519CliBlocks.getD 1 { code := [] } = x25519CliBlk01 := rfl

theorem regL_get (L : List (BitVec 64)) (k : BitVec 5) : regL L k = L.getD k.toNat 0 := rfl
theorem ze_e0 : (0x0e0#12 : BitVec 12).zeroExtend 64 = 224#64 := rfl
theorem ze_13 : (0x0013#16 : BitVec 16).zeroExtend 64 = 19#64 := rfl

section fetch
variable {mpl : MultiPlacement} {m : Memory} (hCL : (prog mpl 1).CodeLoaded m)
include hCL

theorem f01_0 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 0) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.sp) (Arm64.Reg.sp) 0x0e0#12 false) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_4 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 4) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000080#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_8 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 8) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x1b#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000090#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_12 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 12) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x19#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000a0#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_16 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 16) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x17#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000b0#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_20 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 20) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000c0#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_24 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 24) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000d0#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_28 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 28) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000000#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_32 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 32) =
    some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_36 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 36) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x08#5) 0x0013#16 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_40 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 40) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x11#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000010#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_44 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 44) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x05#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000020#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_48 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 48) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x1a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000020#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_52 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 52) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x0d#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000008#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_56 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 56) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_60 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 60) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_64 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 64) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_68 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 68) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_72 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 72) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_76 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 76) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_80 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 80) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_84 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 84) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000060#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_88 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 88) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000010#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_92 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 92) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_96 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 96) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_100 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 100) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_104 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 104) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_108 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 108) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x1e#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_112 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 112) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000018#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_116 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 116) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_120 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 120) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_124 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 124) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_128 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 128) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_132 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 132) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000008#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_136 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 136) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_140 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 140) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_144 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 144) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x17#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_148 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 148) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x15#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_152 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 152) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000038#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_156 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 156) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_160 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 160) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_164 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 164) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x1b#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_168 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 168) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_172 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 172) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000028#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_176 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 176) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_180 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 180) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_184 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 184) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_188 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 188) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000058#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_192 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 192) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_196 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 196) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x03#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_200 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 200) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_204 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 204) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_208 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 208) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000048#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_212 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 212) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_216 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 216) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_220 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 220) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_224 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 224) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000088#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_228 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 228) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_232 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 232) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_236 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 236) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_240 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 240) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000078#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_244 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 244) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_248 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 248) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_252 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 252) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000068#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_256 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 256) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_260 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 260) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_264 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 264) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x19#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000060#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_268 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 268) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_272 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 272) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.gpr 0x0a#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_276 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 276) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.gpr 0x07#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000018#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_280 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 280) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x16#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_284 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 284) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_288 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 288) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x07#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_292 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 292) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x1b#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_296 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 296) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_300 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 300) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x19#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_304 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 304) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x14#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_308 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 308) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x19#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000038#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_312 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 312) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x1c#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_316 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 316) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_320 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 320) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x18#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000008#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_324 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 324) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_328 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 328) =
    some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x09#5) 51) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_332 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 332) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) 0x0007ffffffffffff#64) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_336 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 336) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x0b#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_340 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 340) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x18#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_344 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 344) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x17#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_348 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 348) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_352 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 352) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x1b#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000090#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_356 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 356) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x18#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_360 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 360) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_364 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 364) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000080#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_368 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 368) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x19#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_372 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 372) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x10#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_376 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 376) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x10#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000030#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_380 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 380) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x00#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_384 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 384) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_388 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 388) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000040#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_392 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 392) =
    some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINC) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.CondCode.CC)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_396 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 396) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x16#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_400 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 400) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_404 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 404) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x0f#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_408 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 408) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000028#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_412 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 412) =
    some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x08#5) 51) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_416 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 416) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x17#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_420 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 420) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) 0x0007ffffffffffff#64) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_424 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 424) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_428 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 428) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000048#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_432 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 432) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_436 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 436) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x00#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_440 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 440) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_444 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 444) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x06#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_448 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 448) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x12#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_452 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 452) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_456 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 456) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000050#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_460 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 460) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x01#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_464 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 464) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_468 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 468) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_472 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 472) =
    some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINC) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.CondCode.CC)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_476 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 476) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_480 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 480) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x18#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_484 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 484) =
    some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0b#5) 51) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_488 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 488) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x17#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_492 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 492) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x15#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_496 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 496) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_500 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 500) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x1a#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_504 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 504) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x07#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_508 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 508) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x13#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_512 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 512) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000c0#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_516 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 516) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_520 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 520) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x17#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000b0#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_524 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 524) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_528 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 528) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x19#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000a0#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_532 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 532) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_536 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 536) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x14#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_540 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 540) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_544 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 544) =
    some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINC) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x12#5) (Arm64.CondCode.CC)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_548 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 548) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x12#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000088#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_552 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 552) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_556 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 556) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x11#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000078#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_560 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 560) =
    some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0c#5) 51) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_564 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 564) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000d0#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_568 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 568) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_572 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 572) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x10#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_576 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 576) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x12#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000068#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_580 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 580) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_584 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 584) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x12#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_588 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 588) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_592 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 592) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0a#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_596 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 596) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_600 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 600) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0d#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_604 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 604) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_608 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 608) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x0e#5) 0x0013#16 0) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_612 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 612) =
    some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINC) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.CondCode.CC)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_616 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 616) =
    some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0d#5) 51) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_620 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 620) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x09#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_624 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 624) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSR) 51) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_628 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 628) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) 0x0007ffffffffffff#64) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_632 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 632) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0x0000000000000000#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_636 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 636) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0b#5) 0x0007ffffffffffff#64) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_640 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 640) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0c#5) 0x0007ffffffffffff#64) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_644 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 644) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0x0000000000000010#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_648 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 648) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0d#5) 0x0007ffffffffffff#64) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_652 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 652) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0x0000000000000020#64)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_656 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 656) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.sp) (Arm64.Reg.sp) 0x0e0#12 false) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f01_660 : rawFetch m (mpl.base 1 + BitVec.ofNat 64 660) =
    some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) :=
  fetch_plain blk01 (by decide) hCL (by decide) (by decide) rfl rfl

end fetch

theorem mul_run {mpl : MultiPlacement} {P : State → Prop} {s0 : State} {W : BitVec 64 → Prop}
    {a b out A0 A1 A2 A3 A4 B0 B1 B2 B3 B4 : BitVec 64}
    (hCL : (prog mpl 1).CodeLoaded s0.mem)
    (hrun : s0.status = .Running) (hW : WOwned s0.mem W) (hsp' : (s0.sp - 224#64).toNat % 16 = 0)
    (hstk : ∀ c : BitVec 64, c.toNat + 8 ≤ 224 → AllB W (s0.sp - 224#64 + c) 8)
    (hstk2 : ∀ c : BitVec 64, c.toNat + 16 ≤ 224 → AllB W (s0.sp - 224#64 + c + 8#64) 8)
    (hout : ∀ c : BitVec 64, c.toNat + 8 ≤ 40 → AllB W (out + c) 8)
    (hout2 : ∀ c : BitVec 64, c.toNat + 16 ≤ 40 → AllB W (out + c + 8#64) 8)
    (hrA : ∀ m c, MemOK s0.mem W m → c.toNat + 8 ≤ 40 → m.canRead (a + c) 8 = true)
    (hrA2 : ∀ m c, MemOK s0.mem W m → c.toNat + 16 ≤ 40 → m.canRead (a + c + 8#64) 8 = true)
    (hrB : ∀ m c, MemOK s0.mem W m → c.toNat + 8 ≤ 40 → m.canRead (b + c) 8 = true)
    (hrB2 : ∀ m c, MemOK s0.mem W m → c.toNat + 16 ≤ 40 → m.canRead (b + c + 8#64) 8 = true)
    (hA0 : ∀ m, MemOK s0.mem W m → m.read64 a = A0)
    (hA1 : ∀ m, MemOK s0.mem W m → m.read64 (a + 8#64) = A1)
    (hA2 : ∀ m, MemOK s0.mem W m → m.read64 (a + 16#64) = A2)
    (hA3 : ∀ m, MemOK s0.mem W m → m.read64 (a + 24#64) = A3)
    (hA4 : ∀ m, MemOK s0.mem W m → m.read64 (a + 32#64) = A4)
    (hB0 : ∀ m, MemOK s0.mem W m → m.read64 b = B0)
    (hB1 : ∀ m, MemOK s0.mem W m → m.read64 (b + 8#64) = B1)
    (hB2 : ∀ m, MemOK s0.mem W m → m.read64 (b + 16#64) = B2)
    (hB3 : ∀ m, MemOK s0.mem W m → m.read64 (b + 24#64) = B3)
    (hB4 : ∀ m, MemOK s0.mem W m → m.read64 (b + 32#64) = B4)
    (hbA : A0.toNat < 2 ^ 54 ∧ A1.toNat < 2 ^ 54 ∧ A2.toNat < 2 ^ 54 ∧ A3.toNat < 2 ^ 54 ∧
      A4.toNat < 2 ^ 54)
    (hbB : B0.toNat < 2 ^ 54 ∧ B1.toNat < 2 ^ 54 ∧ B2.toNat < 2 ^ 54 ∧ B3.toNat < 2 ^ 54 ∧
      B4.toNat < 2 ^ 54)
    (ha : s0.regs.regs 0#5 = a) (hb : s0.regs.regs 1#5 = b) (ho : s0.regs.regs 8#5 = out)
    (hP : ∀ (L : List (BitVec 64)) (m : Memory) (ps : PState) (l0 l1 l2 l3 l4 : BitVec 64),
      (∀ k : BitVec 5, 19 ≤ k.toNat → regL L k = s0.regs.regs k) → MemOK s0.mem W m →
      m.read64 out = l0 → m.read64 (out + 8#64) = l1 → m.read64 (out + 16#64) = l2 →
      m.read64 (out + 24#64) = l3 → m.read64 (out + 32#64) = l4 →
      l0.toNat < 2 ^ 52 → l1.toNat < 2 ^ 52 → l2.toNat < 2 ^ 52 → l3.toNat < 2 ^ 52 →
      l4.toNat < 2 ^ 52 →
      fe51Val l0 l1 l2 l3 l4 % p25519 = fe51Val A0 A1 A2 A3 A4 * fe51Val B0 B1 B2 B3 B4 % p25519 →
      P (mkS s0 (s0.regs.regs 30#5) (regL L) s0.sp m ps)) :
    Reach mpl 1 P (mkS s0 (mpl.base 1 + BitVec.ofNat 64 0) (regL [s0.regs.regs 0#5, s0.regs.regs 1#5,
      s0.regs.regs 2#5, s0.regs.regs 3#5, s0.regs.regs 4#5, s0.regs.regs 5#5, s0.regs.regs 6#5,
      s0.regs.regs 7#5, s0.regs.regs 8#5, s0.regs.regs 9#5, s0.regs.regs 10#5, s0.regs.regs 11#5,
      s0.regs.regs 12#5, s0.regs.regs 13#5, s0.regs.regs 14#5, s0.regs.regs 15#5, s0.regs.regs 16#5,
      s0.regs.regs 17#5, s0.regs.regs 18#5, s0.regs.regs 19#5, s0.regs.regs 20#5, s0.regs.regs 21#5,
      s0.regs.regs 22#5, s0.regs.regs 23#5, s0.regs.regs 24#5, s0.regs.regs 25#5, s0.regs.regs 26#5,
      s0.regs.regs 27#5, s0.regs.regs 28#5, s0.regs.regs 29#5, s0.regs.regs 30#5,
      s0.regs.regs 31#5]) s0.sp s0.mem s0.pstate) := by
  rw [ha, hb, ho]
  have hok := memOK_refl s0.mem W
  refine r_subsp hrun hW hok (f01_0 hCL) ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, BitVec.sub_add_cancel]
  refine r_str_sp (by decide) hsp' hrun hW hok (f01_4 hCL) (hstk _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f01_8 hCL) (hstk _ (by decide)) (hstk2 _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f01_12 hCL) (hstk _ (by decide)) (hstk2 _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f01_16 hCL) (hstk _ (by decide)) (hstk2 _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f01_20 hCL) (hstk _ (by decide)) (hstk2 _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f01_24 hCL) (hstk _ (by decide)) (hstk2 _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_ldp_g (by decide) (by decide) (by decide) hrun hW hok (f01_28 hCL) (hrB _ _ hok (by decide)) (hrB2 _ _ hok (by decide)) (fun v28a v28b e28a e28b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e28a e28b ⊢
  rw [hB0 _ hok] at e28a; rw [hB1 _ hok] at e28b; subst v28a v28b
  refine r_movx (by decide) (by decide) hrun hW hok (f01_32 hCL) ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13]
  refine r_movz (by decide) hrun hW hok (f01_36 hCL) ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13]
  refine r_ldp_g (by decide) (by decide) (by decide) hrun hW hok (f01_40 hCL) (hrB _ _ hok (by decide)) (hrB2 _ _ hok (by decide)) (fun v40a v40b e40a e40b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e40a e40b ⊢
  rw [hB2 _ hok] at e40a; rw [hB3 _ hok] at e40b; subst v40a v40b
  refine r_ldr_g (by decide) (by decide) hrun hW hok (f01_44 hCL) (hrB _ _ hok (by decide)) (fun v44 e44 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e44 ⊢
  rw [hB4 _ hok] at e44; subst v44
  refine r_ldr_g (by decide) (by decide) hrun hW hok (f01_48 hCL) (hrA _ _ hok (by decide)) (fun v48 e48 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e48 ⊢
  rw [hA4 _ hok] at e48; subst v48
  refine r_ldr_g (by decide) (by decide) hrun hW hok (f01_52 hCL) (hrA _ _ hok (by decide)) (fun v52 e52 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e52 ⊢
  rw [hA1 _ hok] at e52; subst v52
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_56 hCL) (fun v56 e56 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e56 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_60 hCL) (fun v60 e60 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e60 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_64 hCL) (fun v64 e64 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e64 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_68 hCL) (fun v68 e68 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e68 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_72 hCL) (fun v72 e72 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e72 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_76 hCL) (fun v76 e76 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e76 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_80 hCL) (fun v80 e80 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e80 ⊢
  refine r_str_sp (by decide) hsp' hrun hW hok (f01_84 hCL) (hstk _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_ldp_g (by decide) (by decide) (by decide) hrun hW hok (f01_88 hCL) (hrA _ _ hok (by decide)) (hrA2 _ _ hok (by decide)) (fun v88a v88b e88a e88b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e88a e88b ⊢
  rw [hA2 _ hok] at e88a; rw [hA3 _ hok] at e88b; subst v88a v88b
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_92 hCL) (fun v92 e92 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e92 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_96 hCL) (fun v96 e96 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e96 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_100 hCL) (fun v100 e100 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e100 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_104 hCL) (fun v104 e104 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e104 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_108 hCL) (fun v108 e108 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e108 ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f01_112 hCL) (hstk _ (by decide)) (hstk2 _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_116 hCL) (fun v116 e116 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e116 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_120 hCL) (fun v120 e120 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e120 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_124 hCL) (fun v124 e124 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e124 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_128 hCL) (fun v128 e128 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e128 ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f01_132 hCL) (hstk _ (by decide)) (hstk2 _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_136 hCL) (fun v136 e136 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e136 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_140 hCL) (fun v140 e140 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e140 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_144 hCL) (fun v144 e144 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e144 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_148 hCL) (fun v148 e148 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e148 ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f01_152 hCL) (hstk _ (by decide)) (hstk2 _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_156 hCL) (fun v156 e156 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e156 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_160 hCL) (fun v160 e160 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e160 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_164 hCL) (fun v164 e164 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e164 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_168 hCL) (fun v168 e168 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e168 ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f01_172 hCL) (hstk _ (by decide)) (hstk2 _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_176 hCL) (fun v176 e176 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e176 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_180 hCL) (fun v180 e180 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e180 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_184 hCL) (fun v184 e184 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e184 ⊢
  refine r_str_sp (by decide) hsp' hrun hW hok (f01_188 hCL) (hstk _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_192 hCL) (fun v192 e192 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e192 ⊢
  refine r_ldr_g (by decide) (by decide) hrun hW hok (f01_196 hCL) (hrA _ _ hok (by decide)) (fun v196 e196 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e196 ⊢
  rw [hA0 _ hok] at e196; subst v196
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_200 hCL) (fun v200 e200 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e200 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_204 hCL) (fun v204 e204 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e204 ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f01_208 hCL) (hstk _ (by decide)) (hstk2 _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_212 hCL) (fun v212 e212 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e212 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_216 hCL) (fun v216 e216 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e216 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_220 hCL) (fun v220 e220 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e220 ⊢
  refine r_str_sp (by decide) hsp' hrun hW hok (f01_224 hCL) (hstk _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_228 hCL) (fun v228 e228 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e228 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_232 hCL) (fun v232 e232 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e232 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_236 hCL) (fun v236 e236 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e236 ⊢
  refine r_str_sp (by decide) hsp' hrun hW hok (f01_240 hCL) (hstk _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_244 hCL) (fun v244 e244 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e244 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_248 hCL) (fun v248 e248 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e248 ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f01_252 hCL) (hstk _ (by decide)) (hstk2 _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_256 hCL) (fun v256 e256 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e256 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_260 hCL) (fun v260 e260 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e260 ⊢
  refine r_ldr_sp (by decide) hsp' hrun hW hok (f01_264 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (fun v264 e264 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e264 ⊢
  subst v264
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_268 hCL) (fun v268 e268 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e268 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_272 hCL) (fun v272 e272 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e272 ⊢
  refine r_ldp_sp (by decide) (by decide) hsp' hrun hW hok (f01_276 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (canRead_of_W hW hok (hstk2 _ (by decide))) (fun v276a v276b e276a e276b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e276a e276b ⊢
  subst v276a v276b
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_280 hCL) (fun v280 e280 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e280 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_284 hCL) (fun v284 e284 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e284 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_288 hCL) (fun v288 e288 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e288 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_292 hCL) (fun v292 e292 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e292 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_296 hCL) (fun v296 e296 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e296 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_300 hCL) (fun v300 e300 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e300 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_304 hCL) (fun v304 e304 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e304 ⊢
  refine r_ldr_sp (by decide) hsp' hrun hW hok (f01_308 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (fun v308 e308 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e308 ⊢
  subst v308
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_312 hCL) (fun v312 e312 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e312 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_316 hCL) (fun v316 e316 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e316 ⊢
  refine r_ldr_sp (by decide) hsp' hrun hW hok (f01_320 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (fun v320 e320 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e320 ⊢
  subst v320
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_324 hCL) (fun v324 e324 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e324 ⊢
  refine r_extr (by decide) (by decide) (by decide) hrun hW hok (f01_328 hCL) (fun v328 e328 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e328 ⊢
  refine r_andi (by decide) (by decide) hrun hW hok (f01_332 hCL) (fun v332 e332 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e332 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_336 hCL) (fun v336 e336 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e336 ⊢
  refine r_ldr_sp (by decide) hsp' hrun hW hok (f01_340 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (fun v340 e340 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e340 ⊢
  subst v340
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_344 hCL) (fun v344 e344 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e344 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_348 hCL) (fun v348 e348 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e348 ⊢
  refine r_ldp_sp (by decide) (by decide) hsp' hrun hW hok (f01_352 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (canRead_of_W hW hok (hstk2 _ (by decide))) (fun v352a v352b e352a e352b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e352a e352b ⊢
  subst v352a v352b
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_356 hCL) (fun v356 e356 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e356 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_360 hCL) (fun v360 e360 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e360 ⊢
  refine r_ldr_sp (by decide) hsp' hrun hW hok (f01_364 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (fun v364 e364 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e364 ⊢
  subst v364
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_368 hCL) (fun v368 e368 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e368 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_372 hCL) (fun v372 e372 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e372 ⊢
  refine r_ldr_sp (by decide) hsp' hrun hW hok (f01_376 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (fun v376 e376 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e376 ⊢
  subst v376
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_380 hCL) (fun v380 e380 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e380 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_384 hCL) (fun v384 e384 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e384 ⊢
  refine r_ldr_sp (by decide) hsp' hrun hW hok (f01_388 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (fun v388 e388 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e388 ⊢
  subst v388
  refine r_cinc (by decide) (by decide) hrun hW hok (f01_392 hCL) (fun v392 e392 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e392 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_396 hCL) (fun v396 e396 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e396 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_400 hCL) (fun v400 e400 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e400 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_404 hCL) (fun v404 e404 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e404 ⊢
  refine r_ldr_sp (by decide) hsp' hrun hW hok (f01_408 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (fun v408 e408 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e408 ⊢
  subst v408
  refine r_extr (by decide) (by decide) (by decide) hrun hW hok (f01_412 hCL) (fun v412 e412 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e412 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_416 hCL) (fun v416 e416 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e416 ⊢
  refine r_andi (by decide) (by decide) hrun hW hok (f01_420 hCL) (fun v420 e420 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e420 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_424 hCL) (fun v424 e424 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e424 ⊢
  refine r_ldr_sp (by decide) hsp' hrun hW hok (f01_428 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (fun v428 e428 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e428 ⊢
  subst v428
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_432 hCL) (fun v432 e432 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e432 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_436 hCL) (fun v436 e436 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e436 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_440 hCL) (fun v440 e440 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e440 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_444 hCL) (fun v444 e444 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e444 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_448 hCL) (fun v448 e448 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e448 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_452 hCL) (fun v452 e452 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e452 ⊢
  refine r_ldp_sp (by decide) (by decide) hsp' hrun hW hok (f01_456 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (canRead_of_W hW hok (hstk2 _ (by decide))) (fun v456a v456b e456a e456b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e456a e456b ⊢
  subst v456a v456b
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_460 hCL) (fun v460 e460 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e460 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_464 hCL) (fun v464 e464 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e464 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_468 hCL) (fun v468 e468 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e468 ⊢
  refine r_cinc (by decide) (by decide) hrun hW hok (f01_472 hCL) (fun v472 e472 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e472 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_476 hCL) (fun v476 e476 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e476 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_480 hCL) (fun v480 e480 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e480 ⊢
  refine r_extr (by decide) (by decide) (by decide) hrun hW hok (f01_484 hCL) (fun v484 e484 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e484 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_488 hCL) (fun v488 e488 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e488 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_492 hCL) (fun v492 e492 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e492 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_496 hCL) (fun v496 e496 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e496 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_500 hCL) (fun v500 e500 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e500 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_504 hCL) (fun v504 e504 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e504 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_508 hCL) (fun v508 e508 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e508 ⊢
  refine r_ldp_sp (by decide) (by decide) hsp' hrun hW hok (f01_512 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (canRead_of_W hW hok (hstk2 _ (by decide))) (fun v512a v512b e512a e512b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e512a e512b ⊢
  subst v512a v512b
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_516 hCL) (fun v516 e516 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e516 ⊢
  refine r_ldp_sp (by decide) (by decide) hsp' hrun hW hok (f01_520 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (canRead_of_W hW hok (hstk2 _ (by decide))) (fun v520a v520b e520a e520b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e520a e520b ⊢
  subst v520a v520b
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_524 hCL) (fun v524 e524 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e524 ⊢
  refine r_ldp_sp (by decide) (by decide) hsp' hrun hW hok (f01_528 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (canRead_of_W hW hok (hstk2 _ (by decide))) (fun v528a v528b e528a e528b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e528a e528b ⊢
  subst v528a v528b
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f01_532 hCL) (fun v532 e532 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e532 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_536 hCL) (fun v536 e536 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e536 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_540 hCL) (fun v540 e540 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e540 ⊢
  refine r_cinc (by decide) (by decide) hrun hW hok (f01_544 hCL) (fun v544 e544 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e544 ⊢
  refine r_ldr_sp (by decide) hsp' hrun hW hok (f01_548 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (fun v548 e548 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e548 ⊢
  subst v548
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f01_552 hCL) (fun v552 e552 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e552 ⊢
  refine r_ldr_sp (by decide) hsp' hrun hW hok (f01_556 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (fun v556 e556 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e556 ⊢
  subst v556
  refine r_extr (by decide) (by decide) (by decide) hrun hW hok (f01_560 hCL) (fun v560 e560 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e560 ⊢
  refine r_ldp_sp (by decide) (by decide) hsp' hrun hW hok (f01_564 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (canRead_of_W hW hok (hstk2 _ (by decide))) (fun v564a v564b e564a e564b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e564a e564b ⊢
  subst v564a v564b
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_568 hCL) (fun v568 e568 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e568 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_572 hCL) (fun v572 e572 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e572 ⊢
  refine r_ldp_sp (by decide) (by decide) hsp' hrun hW hok (f01_576 hCL) (canRead_of_W hW hok (hstk _ (by decide))) (canRead_of_W hW hok (hstk2 _ (by decide))) (fun v576a v576b e576a e576b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow] at e576a e576b ⊢
  subst v576a v576b
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_580 hCL) (fun v580 e580 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e580 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_584 hCL) (fun v584 e584 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e584 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_588 hCL) (fun v588 e588 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e588 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_592 hCL) (fun v592 e592 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e592 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_596 hCL) (fun v596 e596 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e596 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f01_600 hCL) (fun v600 e600 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e600 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f01_604 hCL) (fun v604 e604 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e604 ⊢
  refine r_movz (by decide) hrun hW hok (f01_608 hCL) ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13]
  refine r_cinc (by decide) (by decide) hrun hW hok (f01_612 hCL) (fun v612 e612 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e612 ⊢
  refine r_extr (by decide) (by decide) (by decide) hrun hW hok (f01_616 hCL) (fun v616 e616 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e616 ⊢
  refine r_madd (by decide) (by decide) (by decide) (by decide) hrun hW hok (f01_620 hCL) (fun v620 e620 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e620 ⊢
  refine r_add_lsr (by decide) (by decide) (by decide) hrun hW hok (f01_624 hCL) (fun v624 e624 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e624 ⊢
  refine r_andi (by decide) (by decide) hrun hW hok (f01_628 hCL) (fun v628 e628 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e628 ⊢
  refine r_stp_g (by decide) (by decide) (by decide) hrun hW hok (f01_632 hCL) (hout _ (by decide)) (hout2 _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_andi (by decide) (by decide) hrun hW hok (f01_636 hCL) (fun v636 e636 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e636 ⊢
  refine r_andi (by decide) (by decide) hrun hW hok (f01_640 hCL) (fun v640 e640 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e640 ⊢
  refine r_stp_g (by decide) (by decide) (by decide) hrun hW hok (f01_644 hCL) (hout _ (by decide)) (hout2 _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_andi (by decide) (by decide) hrun hW hok (f01_648 hCL) (fun v648 e648 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e648 ⊢
  refine r_str_g (by decide) (by decide) hrun hW hok (f01_652 hCL) (hout _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_addsp hrun hW hok (f01_656 hCL) ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, BitVec.sub_add_cancel]
  refine r_ret hrun hW hok (f01_660 hCL) ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13]
  obtain ⟨r0b, r1b, r2b, r3b, r4b, hval⟩ := mul_arith e56 e60 e64 e68 e72 e76 e200 e244 e96 e124 e100 e164 e80 e92 e116 e128 e268 e256 e120 e144 e136 e108 e204 e168 e140 e156 e348 e284 e104 e160 e180 e184 e220 e248 e176 e192 e416 e400 e232 e148 e296 e324 e432 e476 e212 e228 e516 e496 e216 e236 e452 e464 e552 e532 e260 e272 e280 e288 e292 e300 e304 e312 e328 e332 e316 e336 e344 e356 e360 e368 e372 e380 e384 e392 e412 e420 e396 e404 e424 e436 e440 e444 e448 e460 e468 e472 e484 e636 e480 e488 e492 e500 e504 e508 e524 e536 e540 e544 e560 e640 e568 e572 e580 e584 e588 e592 e596 e600 e604 e612 e616 e648 e620 e628 e624 hbA hbB
  refine hP _ _ _ v628 v624 v636 v640 v648
    (regL_callee _ _ (fun j h1 h2 => by interval_cases j <;> rfl)) hok ?_ ?_ ?_ ?_ ?_ r0b r1b r2b r3b r4b hval
  · simp only [read64_write64_far, read64_write64_same, far_add_left_iff, far_add_right_iff,
      far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod,
      Nat.reducePow]
  · simp only [read64_write64_far, read64_write64_same, far_add_left_iff, far_add_right_iff,
      far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod,
      Nat.reducePow]
  · simp only [read64_write64_far, read64_write64_same, far_add_left_iff, far_add_right_iff,
      far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod,
      Nat.reducePow]
  · simp only [read64_write64_far, read64_write64_same, far_add_left_iff, far_add_right_iff,
      far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod,
      Nat.reducePow]
  · simp only [read64_write64_far, read64_write64_same, far_add_left_iff, far_add_right_iff,
      far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod,
      Nat.reducePow]

end X25519Dalek.Field
end

section
/-! # Buffers: byte cells of points-to assertions, 64-bit words of byte lists -/

namespace X25519Dalek.Field

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-- Every heap of `P` holds byte `bs[i]` at `a + i`, as a cell of kind `k` (read-write or
read-only). -/
def InCells (P : SepProp) (a : BitVec 64) (bs : List (BitVec 8)) (k : BitVec 8 → HeapCell) : Prop :=
  ∀ h, P.holds h → ∀ i (hi : i < bs.length), h.phys (a + BitVec.ofNat 64 i) = some (k bs[i])

/-- Read-write and read-only cells. -/
def GoodKind (k : BitVec 8 → HeapCell) : Prop := k = HeapCell.rw ∨ k = HeapCell.ro

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

theorem inCells_rw (bs : List (BitVec 8)) (a : BitVec 64) : InCells (a ↦ₛ bs) a bs HeapCell.rw :=
  fun h hh i hi => rwCells_bytes bs a h hh i hi

theorem inCells_ro (bs : List (BitVec 8)) (a : BitVec 64) : InCells (a ↦ᵣ bs) a bs HeapCell.ro :=
  fun h hh i hi => roCells_bytes bs a h hh i hi

/-- In `A ∗ Q`, the bytes of `A` are in memory, readable, and outside what `Q` owns. -/
theorem bytes_of_sat {A Q R C : SepProp} {φ : Prop} {m0 : Memory} {W : BitVec 64 → Prop}
    {a : BitVec 64} {bs : List (BitVec 8)} {k : BitVec 8 → HeapCell}
    (hs : m0 ⊨ ((⌜φ⌝ ∗ (A ∗ Q)) ∗ C) ∗ R) (hA : InCells A a bs k) (hk : GoodKind k)
    (hQ : OwnsRW Q W) :
    ∀ i (hi : i < bs.length), m0.read8 (a + BitVec.ofNat 64 i) = bs[i] ∧
      (m0.perm (a + BitVec.ofNat 64 i)).r = true ∧ m0.isLazyFree (a + BitVec.ofNat 64 i) = false ∧
      ¬ W (a + BitVec.ofNat 64 i) := by
  intro i hi
  obtain ⟨h, hh, hm⟩ := hs
  have c : h.phys (a + BitVec.ofNat 64 i) = some (k bs[i]) :=
    cell_sep_left hh fun h1 p1 => cell_sep_left p1 fun h2 p2 => cell_sep_right p2 fun h3 p3 =>
      cell_sep_left p3 fun h4 p4 => hA h4 p4 i hi
  have nw : ¬ W (a + BitVec.ofNat 64 i) := by
    obtain ⟨_, _, _, rfl, p1, _⟩ := hh
    obtain ⟨_, _, _, rfl, p2, _⟩ := p1
    obtain ⟨_, _, _, rfl, _, p3⟩ := p2
    exact not_W_of p3 hQ fun h4 p4 => by simp [hA h4 p4 i hi]
  have := hm.1 _ _ c
  rcases hk with rfl | rfl
  · simp only at this
    exact ⟨this.1, by rw [this.2.1]; rfl, this.2.2, nw⟩
  · simp only at this
    exact ⟨this.1, this.2.1, this.2.2, nw⟩

/-! ## 64-bit words of byte lists -/

theorem readLE8_eq (bs : List (BitVec 8)) (off : Nat) :
    ByteSlice.readLE bs off 8 = bs.getD (off + 7) 0#8 ++ bs.getD (off + 6) 0#8 ++
      bs.getD (off + 5) 0#8 ++ bs.getD (off + 4) 0#8 ++ bs.getD (off + 3) 0#8 ++
      bs.getD (off + 2) 0#8 ++ bs.getD (off + 1) 0#8 ++ bs.getD (off + 0) 0#8 := by
  simp only [ByteSlice.readLE]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append,
    BitVec.zeroExtend_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero]
  interval_cases i <;> simp

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

end X25519Dalek.Field
end

section
/-! # `<&FieldElement51 as Mul>::mul`: the three contracts -/

namespace X25519Dalek.Field

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-- The multiplication contract with the assertions `PA`, `PB` for the two operands. -/
abbrev mulSpecG (PA PB : BitVec 64 → List (BitVec 8) → SepProp) : Spec
  (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8)) :=
{
  pre :=
    fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
      (s0 : State) =>
    match x with
    | (out, a, b, out_bs, a_bs, b_bs) =>
      ⌜s0.readReg64 Reg.x8 = out ∧
            s0.readReg64 Reg.x0 = a ∧
              s0.readReg64 Reg.x1 = b ∧
                out_bs.length = 40 ∧ fe51LimbsBounded a_bs (2 ^ 54) ∧ fe51LimbsBounded b_bs (2 ^ 54)⌝ ∗
        PA a a_bs ∗ PB b b_bs ∗ out ↦ₛ out_bs ∗ stackFrame s0 224,
  post :=
    fun (x : BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8) × List (BitVec 8))
      (s0 sf : State) =>
    match x with
    | (out, a, b, out_bs, a_bs, b_bs) =>
      PA a a_bs ∗
        PB b b_bs ∗
          stackFrame sf 224 ∗
            ∃∗ res_bs : List (BitVec 8),
              out ↦ₛ res_bs ∗
                ⌜fe51LimbsBounded res_bs (2 ^ 52) ∧
                    fe51ValOfBytes res_bs % p25519 =
                      fe51ValOfBytes a_bs * fe51ValOfBytes b_bs % p25519⌝ }

theorem sep_mono_r {P Q Q' : SepProp} (h : Q ⊢ Q') : (P ∗ Q) ⊢ (P ∗ Q') := by
  rintro _ ⟨h1, h2, hd, rfl, p, q⟩
  exact ⟨h1, h2, hd, rfl, p, h _ q⟩

theorem ent_exists_pure {α : Type} {P : α → SepProp} {ψ : α → Prop} (x : α) (h : ψ x) :
    P x ⊢ ∃∗ y, P y ∗ ⌜ψ y⌝ := by
  intro k hk
  exact ⟨x, k, Heap.empty, disjoint_symm (disjoint_empty k), (union_empty k).symm, hk, rfl, h⟩

theorem bytesAt_eq {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)}
    (h : ∀ i (hi : i < bs.length), m.read8 (a + BitVec.ofNat 64 i) = bs[i]) :
    bytesAt m a bs.length = bs := by
  apply List.ext_getElem (bytesAt_length _ _ _)
  intro i h1 h2
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  exact h i h2

theorem rf_rw_same (m : Memory) (a : BitVec 64) (bs : List (BitVec 8))
    (h : ∀ i (hi : i < bs.length), m.read8 (a + BitVec.ofNat 64 i) = bs[i]) :
    Rf m (a ↦ₛ bs) (a ↦ₛ bs) := by
  have := rf_bytes m bs a
  rwa [bytesAt_eq h] at this

theorem mul_ok (PA PB : BitVec 64 → List (BitVec 8) → SepProp) (kA kB : BitVec 8 → HeapCell)
    (hkA : GoodKind kA) (hkB : GoodKind kB)
    (hcA : ∀ a bs, InCells (PA a bs) a bs kA) (hcB : ∀ a bs, InCells (PB a bs) a bs kB)
    (hrfA : ∀ m a bs, (∀ i (hi : i < bs.length), m.read8 (a + BitVec.ofNat 64 i) = bs[i]) →
      Rf m (PA a bs) (PA a bs))
    (hrfB : ∀ m a bs, (∀ i (hi : i < bs.length), m.read8 (a + BitVec.ofNat 64 i) = bs[i]) →
      Rf m (PB a bs) (PB a bs)) :
    fnOk "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul"
      (fun _ => mulSpecG PA PB) := by
  refine ⟨1, 0, rfl, fun mpl _ => ?_⟩
  rintro ⟨out, a, b, out_bs, a_bs, b_bs⟩ R s0 hpc hrun hpre hal hCL
  have hfa : x25519CliMultiLib.fnAddr mpl
      "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" =
      mpl.base 1 + BitVec.ofNat 64 0 := rfl
  rw [hfa] at hpc
  change s0.mem ⊨ ((⌜s0.readReg64 Reg.x8 = out ∧ s0.readReg64 Reg.x0 = a ∧ s0.readReg64 Reg.x1 = b ∧
      out_bs.length = 40 ∧ fe51LimbsBounded a_bs (2 ^ 54) ∧ fe51LimbsBounded b_bs (2 ^ 54)⌝ ∗
      (PA a a_bs ∗ (PB b b_bs ∗ (out ↦ₛ out_bs ∗ memRegion (s0.sp - BitVec.ofNat 64 224) 224)))) ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝) ∗ R at hpre
  have hφ := pure_of_sat (P := PA a a_bs ∗ _) (by rw [sepConj_assoc] at hpre; exact hpre)
  obtain ⟨hx8, hx0, hx1, hlo, hba, hbb⟩ := hφ
  set W : BitVec 64 → Prop := fun x => InRegion (s0.sp - BitVec.ofNat 64 224) 224 x ∨ InRegion out 40 x
    with hWdef
  have hOwnQ : OwnsRW (out ↦ₛ out_bs ∗ memRegion (s0.sp - BitVec.ofNat 64 224) 224) W := by
    refine ownsRW_or (ownsRW_sep_right (ownsRW_region _ _)) ?_
    have := ownsRW_sep_left (Q := memRegion (s0.sp - BitVec.ofNat 64 224) 224) (ownsRW_bytes out_bs out)
    rwa [hlo] at this
  have hOwnB := ownsRW_sep_right (P := PB b b_bs) hOwnQ
  have hOwnA := ownsRW_sep_right (P := PA a a_bs) hOwnB
  have hW := wowned_of hpre (ownsRW_sep_left (ownsRW_sep_right hOwnA))
  have bA := bytes_of_sat hpre (hcA a a_bs) hkA hOwnB
  have hpre' := hpre
  rw [sepConj_left_comm (PA a a_bs)] at hpre'
  have bB := bytes_of_sat hpre' (hcB b b_bs) hkB (ownsRW_sep_right (P := PA a a_bs) hOwnQ)
  have la : a_bs.length = 40 := hba.1
  have lb : b_bs.length = 40 := hbb.1
  have hsp : s0.sp.toNat % 16 = 0 := (spAligned_iff s0).1 hal
  have hsp' : (s0.sp - 224#64).toNat % 16 = 0 := sp_sub_aligned hsp 224 rfl (by decide)
  have hstk : ∀ c : BitVec 64, c.toNat + 8 ≤ 224 → AllB W (s0.sp - 224#64 + c) 8 := by
    intro c hc j hj; left; unfold InRegion
    rw [show s0.sp - 224#64 + c + BitVec.ofNat 64 j - (s0.sp - BitVec.ofNat 64 224) =
      c + BitVec.ofNat 64 j by bv_omega, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hstk2 : ∀ c : BitVec 64, c.toNat + 16 ≤ 224 → AllB W (s0.sp - 224#64 + c + 8#64) 8 := by
    intro c hc j hj; left; unfold InRegion
    rw [show s0.sp - 224#64 + c + 8#64 + BitVec.ofNat 64 j - (s0.sp - BitVec.ofNat 64 224) =
      c + BitVec.ofNat 64 (8 + j) by bv_omega, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hout : ∀ c : BitVec 64, c.toNat + 8 ≤ 40 → AllB W (out + c) 8 := by
    intro c hc j hj; right; unfold InRegion
    rw [show out + c + BitVec.ofNat 64 j - out = c + BitVec.ofNat 64 j by bv_omega,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hout2 : ∀ c : BitVec 64, c.toNat + 16 ≤ 40 → AllB W (out + c + 8#64) 8 := by
    intro c hc j hj; right; unfold InRegion
    rw [show out + c + 8#64 + BitVec.ofNat 64 j - out = c + BitVec.ofNat 64 (8 + j) by bv_omega,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hrA : ∀ m c, MemOK s0.mem W m → c.toNat + 8 ≤ 40 → m.canRead (a + c) 8 = true := by
    intro m c hok hc
    have := canRead_buf bA hok c.toNat (by omega)
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  have hrA2 : ∀ m c, MemOK s0.mem W m → c.toNat + 16 ≤ 40 → m.canRead (a + c + 8#64) 8 = true := by
    intro m c hok hc
    have := canRead_buf bA hok (c.toNat + 8) (by omega)
    rwa [show a + BitVec.ofNat 64 (c.toNat + 8) = a + c + 8#64 by bv_omega] at this
  have hrB : ∀ m c, MemOK s0.mem W m → c.toNat + 8 ≤ 40 → m.canRead (b + c) 8 = true := by
    intro m c hok hc
    have := canRead_buf bB hok c.toNat (by omega)
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  have hrB2 : ∀ m c, MemOK s0.mem W m → c.toNat + 16 ≤ 40 → m.canRead (b + c + 8#64) 8 = true := by
    intro m c hok hc
    have := canRead_buf bB hok (c.toNat + 8) (by omega)
    rwa [show b + BitVec.ofNat 64 (c.toNat + 8) = b + c + 8#64 by bv_omega] at this
  have rd : ∀ (x : BitVec 64) (bs : List (BitVec 8)), (∀ i (hi : i < bs.length),
      s0.mem.read8 (x + BitVec.ofNat 64 i) = bs[i] ∧ (s0.mem.perm (x + BitVec.ofNat 64 i)).r = true ∧
      s0.mem.isLazyFree (x + BitVec.ofNat 64 i) = false ∧ ¬ W (x + BitVec.ofNat 64 i)) →
      bs.length = 40 → ∀ off, off + 8 ≤ 40 → ∀ m, MemOK s0.mem W m →
      m.read64 (x + BitVec.ofNat 64 off) = ByteSlice.readLE bs off 8 :=
    fun x bs hb hl off ho m hok => read64_buf hb hok off (by omega)
  have ha : s0.regs.regs 0#5 = a := by simpa [State.readReg64, RegFile.read] using hx0
  have hb : s0.regs.regs 1#5 = b := by simpa [State.readReg64, RegFile.read] using hx1
  have ho : s0.regs.regs 8#5 = out := by simpa [State.readReg64, RegFile.read] using hx8
  show Reach mpl 1 _ s0
  apply reach_start
  rw [hpc, regL_init s0.regs.regs]
  refine mul_run hCL hrun hW hsp' hstk hstk2 hout hout2 hrA hrA2 hrB hrB2
    (fun m hok => by simpa using rd a a_bs bA la 0 (by omega) m hok)
    (fun m hok => rd a a_bs bA la 8 (by omega) m hok)
    (fun m hok => rd a a_bs bA la 16 (by omega) m hok)
    (fun m hok => rd a a_bs bA la 24 (by omega) m hok)
    (fun m hok => rd a a_bs bA la 32 (by omega) m hok)
    (fun m hok => by simpa using rd b b_bs bB lb 0 (by omega) m hok)
    (fun m hok => rd b b_bs bB lb 8 (by omega) m hok)
    (fun m hok => rd b b_bs bB lb 16 (by omega) m hok)
    (fun m hok => rd b b_bs bB lb 24 (by omega) m hok)
    (fun m hok => rd b b_bs bB lb 32 (by omega) m hok)
    hba.2 hbb.2 ha hb ho ?_
  intro L m ps l0 l1 l2 l3 l4 hcal hok e0 e1 e2 e3 e4 b0 b1 b2 b3 b4 hval
  refine outcome_of hrun hcal (frame hpre hok (ownsRW_sep_left (ownsRW_sep_right hOwnA)) (rf_mono (rf_sep (rf_sep (rf_pure' (fun _ => trivial))
    (rf_sep (hrfA m a a_bs fun i hi => ?_) (rf_sep (hrfB m b b_bs fun i hi => ?_)
      (rf_sep (rf_bytes m out_bs out) (rf_region _ _ _))))) (rf_pure' (fun _ => trivial))) ?_))
  · rw [(hok _).2.2.2 (bA i hi).2.2.2]; exact (bA i hi).1
  · rw [(hok _).2.2.2 (bB i hi).2.2.2]; exact (bB i hi).1
  · rw [sepConj_pure_true, sepConj_comm, sepConj_pure_true, hlo]
    refine sep_mono_r (sep_mono_r ?_)
    rw [sepConj_comm]
    refine sep_mono_r (ent_exists_pure (P := fun res => out ↦ₛ res) (bytesAt m out 40) ⟨?_, ?_⟩)
    · refine ⟨bytesAt_length _ _ _, ?_, ?_, ?_, ?_, ?_⟩
      · rw [readLE_bytesAt _ _ _ _ (by omega)]; simpa [e0] using b0
      · rw [readLE_bytesAt _ _ _ _ (by omega)]; rw [show out + BitVec.ofNat 64 8 = out + 8#64 from rfl, e1]; exact b1
      · rw [readLE_bytesAt _ _ _ _ (by omega)]; rw [show out + BitVec.ofNat 64 16 = out + 16#64 from rfl, e2]; exact b2
      · rw [readLE_bytesAt _ _ _ _ (by omega)]; rw [show out + BitVec.ofNat 64 24 = out + 24#64 from rfl, e3]; exact b3
      · rw [readLE_bytesAt _ _ _ _ (by omega)]; rw [show out + BitVec.ofNat 64 32 = out + 32#64 from rfl, e4]; exact b4
    · unfold fe51ValOfBytes
      rw [readLE_bytesAt _ _ _ _ (by omega), readLE_bytesAt _ _ _ _ (by omega),
        readLE_bytesAt _ _ _ _ (by omega), readLE_bytesAt _ _ _ _ (by omega),
        readLE_bytesAt _ _ _ _ (by omega)]
      rw [show out + BitVec.ofNat 64 0 = out by simp, e0,
        show out + BitVec.ofNat 64 8 = out + 8#64 from rfl, e1,
        show out + BitVec.ofNat 64 16 = out + 16#64 from rfl, e2,
        show out + BitVec.ofNat 64 24 = out + 24#64 from rfl, e3,
        show out + BitVec.ofNat 64 32 = out + 32#64 from rfl, e4]
      exact hval

theorem fnOk_fe51_mul_dev :
    fnOk "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" (fun _ => fe51MulSpec) ∧
      fnOk "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" (fun _ => fe51MulRoRightSpec) ∧
      fnOk "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" (fun _ => fe51MulRoLeftSpec) :=
  ⟨mul_ok (fun a bs => a ↦ₛ bs) (fun a bs => a ↦ₛ bs) HeapCell.rw HeapCell.rw (Or.inl rfl) (Or.inl rfl)
      (fun a bs => inCells_rw bs a) (fun a bs => inCells_rw bs a) rf_rw_same rf_rw_same,
   mul_ok (fun a bs => a ↦ₛ bs) (fun a bs => a ↦ᵣ bs) HeapCell.rw HeapCell.ro (Or.inl rfl) (Or.inr rfl)
      (fun a bs => inCells_rw bs a) (fun a bs => inCells_ro bs a) rf_rw_same (fun m a bs _ => rf_ro m bs a),
   mul_ok (fun a bs => a ↦ᵣ bs) (fun a bs => a ↦ₛ bs) HeapCell.ro HeapCell.rw (Or.inr rfl) (Or.inl rfl)
      (fun a bs => inCells_ro bs a) (fun a bs => inCells_rw bs a) (fun m a bs _ => rf_ro m bs a) rf_rw_same⟩

end X25519Dalek.Field
end

theorem solution :
    X25519Dalek.fnOk "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" (fun _ => X25519Dalek.fe51MulSpec) ∧
      X25519Dalek.fnOk "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" (fun _ => X25519Dalek.fe51MulRoRightSpec) ∧
      X25519Dalek.fnOk "<&curve25519_dalek::backend::serial::u64::field::FieldElement51 as core::ops::arith::Mul>::mul" (fun _ => X25519Dalek.fe51MulRoLeftSpec) :=
  X25519Dalek.Field.fnOk_fe51_mul_dev
