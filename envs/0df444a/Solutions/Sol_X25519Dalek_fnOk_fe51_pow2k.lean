-- Prove2me | solution 1 for X25519Dalek.fnOk_fe51_pow2k
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T10:48:02.768838+00:00
-- url     : https://prove2.me/submissions/66daec7f-f8d1-4fb0-a032-d7d30ecf0990

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

theorem awc_add (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
  simp only [AddWithCarry64, Bool.false_eq_true, if_false]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_add, BitVec.toNat_ofNat]
  have hx := x.isLt; have hy := y.isLt
  omega

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

/-- `ADDS Xd, Xn, Xm, LSL #k`. -/
theorem ex_adds_lsl {d n k : BitVec 5} {a : Nat} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hk : k ≠ 31#5) :
    execInstWithSvc svc (.addSubShift .W64 .ADDS (.gpr d) (.gpr n) (.gpr k) .LSL a) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d (r n + (r k <<< (a % 64)))) sp m
        (AddWithCarry64 (r n) (r k <<< (a % 64)) false).2 := by
  simp only [execInstWithSvc, execAddSubShift, State.writeReg, State.readReg,
    rd_gpr' _ _ _ _ _ _ _ hn, rd_gpr' _ _ _ _ _ _ _ hk, shiftVal, shift64, evalAddSub_adds,
    wr_gpr _ _ _ _ _ _ _ _ hd, mkS_setPState, mkS_advancePC]

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

theorem regL_get (L : List (BitVec 64)) (k : BitVec 5) : regL L k = L.getD k.toNat 0 := rfl
theorem ze_e0 : (0x0e0#12 : BitVec 12).zeroExtend 64 = 224#64 := rfl
theorem ze_13 : (0x0013#16 : BitVec 16).zeroExtend 64 = 19#64 := rfl

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

theorem r_adds_lsl {d a b : BitVec 5} {k : Nat} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.addSubShift .W64 .ADDS (.gpr d) (.gpr a) (.gpr b) .LSL k))
    (h : ∀ t, t = r a + (r b <<< (k % 64)) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m
        (AddWithCarry64 (r a) (r b <<< (k % 64)) false).2)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_adds_lsl hd ha hb, pc_add4]; exact h _ rfl)

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

theorem r_ret
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.ret (.gpr 30#5)))
    (h : P (mkS s (r 30#5) r sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) :=
  reach_mk hrun hW hok hf (by rw [ex_ret]; exact reach_done h)

/-! ### Loads and stores, with base `sp` (aligned) or a general register -/

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

end X25519Dalek.Field
end

section
/-! # More instruction shapes: pre/post-indexed stack access, 32-bit `SUBS #1`, `B.NE` -/

namespace X25519Dalek.Field

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

theorem awc32_sub (x y : BitVec 32) : (AddWithCarry32 x (~~~y) true).1 = x - y := by
  simp only [AddWithCarry32, if_true]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have hx := x.isLt; have hy := y.isLt
  omega

theorem awc32_sub_z (x y : BitVec 32) :
    (AddWithCarry32 x (~~~y) true).2.z = decide (x - y = 0#32) := by
  rw [show (AddWithCarry32 x (~~~y) true).2.z = ((AddWithCarry32 x (~~~y) true).1 == 0#32) from rfl,
    awc32_sub]
  by_cases h : x - y = 0#32 <;> simp [h]

theorem one12 : BitVec.truncate 32 (BitVec.zeroExtend 64 (1#12 : BitVec 12)) = 1#32 := rfl

section ssa
variable {mpl : MultiPlacement} {i : Nat} {P : State → Prop} {s : State} {pcb : BitVec 64}
  {n : Nat} {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {m m0 : Memory} {ps : PState}
  {W : BitVec 64 → Prop}

theorem r_str_pre_sp {t : BitVec 5} {off : BitVec 64} (ht : t ≠ 31#5) (hsp : sp.toNat % 16 = 0)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.str .X64 (.gpr t) (.PreIndex .sp off)))
    (hw : AllB W (sp + off) 8)
    (h : MemOK m0 W (m.write64 (sp + off) (r t)) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r (sp + off) (m.write64 (sp + off) (r t)) ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  refine reach_mk hrun hW hok hf ?_
  have hal := checkSP s (pcb + BitVec.ofNat 64 n) r sp m ps hsp
  have hwr := canWrite_of hW hok hw
  have e : execInstWithSvc (evalSvc Syscall.standard) (.str .X64 (.gpr t) (.PreIndex .sp off))
      (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) =
      mkS s (pcb + BitVec.ofNat 64 (n + 4)) r (sp + off) (m.write64 (sp + off) (r t)) ps := by
    show execStr .X64 (.gpr t) (.PreIndex .sp off) _ = _
    simp only [execStr, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
      Bool.false_eq_true, if_false, evalAddrMode, rd_sp, mkS_mem, MemWidth.bytes, hwr,
      rd_gpr' _ _ _ _ _ _ _ ht, Memory.writeSized, mkS_setMem, wr_sp, mkS_advancePC, pc_add4]
  rw [e]; exact h (memOK_write64 hW hok hw _)

theorem r_ldr_post_sp {d : BitVec 5} {off : BitVec 64} (hd : d ≠ 31#5) (hsp : sp.toNat % 16 = 0)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.ldr .W64 .X64 false (.gpr d) (.PostIndex .sp off)))
    (hrd : m.canRead sp 8 = true)
    (h : ∀ t, t = m.read64 sp →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) (sp + off) m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  refine reach_mk hrun hW hok hf ?_
  have hal := checkSP s (pcb + BitVec.ofNat 64 n) r sp m ps hsp
  have e : execInstWithSvc (evalSvc Syscall.standard) (.ldr .W64 .X64 false (.gpr d) (.PostIndex .sp off))
      (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) =
      mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d (m.read64 sp)) (sp + off) m ps := by
    show execLdr .W64 .X64 false (.gpr d) (.PostIndex .sp off) _ = _
    simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
      Bool.false_eq_true, if_false, evalAddrMode, rd_sp, mkS_mem, MemWidth.bytes, hrd,
      Memory.readSized, wr_sp, State.writeReg, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC, pc_add4]
  rw [e]; exact h _ rfl

/-- `SUBS Wd, Wn, #1`. -/
theorem r_subs1 {d a : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.addSubImm .W32 .SUBS (.gpr d) (.gpr a) 0x001#12 false))
    (h : ∀ t ps', t = (BitVec.truncate 32 (r a) - 1#32).zeroExtend 64 →
      ps'.z = decide (BitVec.truncate 32 (r a) - 1#32 = 0#32) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d t) sp m ps')) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  refine reach_mk hrun hW hok hf ?_
  simp only [execInstWithSvc, execAddSubImm, State.readReg, State.readReg32,
    rd_gpr' _ _ _ _ _ _ _ ha, evalAddSub, Bool.false_eq_true, if_false, if_true, State.writeReg,
    wr_gpr _ _ _ _ _ _ _ _ hd, mkS_setPState, mkS_advancePC, pc_add4]
  refine h _ _ ?_ ?_
  · rw [awc32_sub, one12]
    apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]
  · rw [awc32_sub_z, one12,
      show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (r a))) = BitVec.truncate 32 (r a) by
        apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]]

theorem r_bne_taken {off : BitVec 64} {pc' : BitVec 64} (hz : ps.z = false)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.bCond .NE off))
    (hpc : pcb + BitVec.ofNat 64 n + off = pc')
    (h : Reach mpl i P (mkS s pc' r sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  refine reach_mk hrun hW hok hf ?_
  show Reach mpl i P (if ConditionHolds .NE (mkS s _ r sp m ps).pstate then _ else _)
  simp only [ConditionHolds, mkS_pstate, hz, Bool.not_false, if_true, mkS_setPC, mkS_pc, hpc]
  exact h

theorem r_bne_not {off : BitVec 64} (hz : ps.z = true)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.bCond .NE off))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  refine reach_mk hrun hW hok hf ?_
  show Reach mpl i P (if ConditionHolds .NE (mkS s _ r sp m ps).pstate then _ else _)
  simp only [ConditionHolds, mkS_pstate, hz, Bool.not_true, Bool.false_eq_true, if_false,
    mkS_advancePC, pc_add4]
  exact h

end ssa

end X25519Dalek.Field

namespace X25519Dalek.Field

open Arm64 Arm64.Obj

theorem far_of_ne {a b : BitVec 64}
    (h : ∀ j k : Nat, j < 8 → k < 8 → a + BitVec.ofNat 64 j ≠ b + BitVec.ofNat 64 k) : Far a b := by
  unfold Far
  constructor
  · by_contra hc
    apply h (b - a).toNat 0 (by omega) (by omega)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; simp; bv_omega
  · by_contra hc
    apply h 0 (a - b).toNat (by omega) (by omega)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; simp; bv_omega

/-- The outcome when the callee-saved registers `x19`–`x30` agree with the entry state. -/
theorem outcome_of' {α : Type} {spec : Spec α} {x : α} {R : SepProp} {s0 : State}
    {r : BitVec 5 → BitVec 64} {m : Memory} {ps : PState}
    (hrun : s0.status = .Running)
    (hr : ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 31 → r k = s0.regs.regs k)
    (hpost : m ⊨ spec.post x s0 (mkS s0 (s0.regs.regs 30#5) r s0.sp m ps) ∗ R) :
    SubroutineOutcome spec x R s0 (mkS s0 (s0.regs.regs 30#5) r s0.sp m ps) := by
  refine Or.inl ⟨⟨?_, rfl, hrun⟩, ⟨rfl, ?_⟩, hpost⟩
  · simp [State.readReg64, RegFile.read]
  · have e : ∀ k : BitVec 5, 19 ≤ k.toNat → k ≠ 31#5 →
        (mkS s0 (s0.regs.regs 30#5) r s0.sp m ps).readReg64 (.gpr k) = s0.readReg64 (.gpr k) := by
      intro k hk1 hk2
      have hk3 : k.toNat < 31 := by
        have := k.isLt; have : k.toNat ≠ 31 := fun h => hk2 (BitVec.eq_of_toNat_eq h); omega
      rw [rd_gpr, if_neg hk2, hr k hk1 hk3]
      simp [State.readReg64, RegFile.read, hk2]
    exact ⟨e 19#5 (by decide) (by decide), e 20#5 (by decide) (by decide),
      e 21#5 (by decide) (by decide), e 22#5 (by decide) (by decide),
      e 23#5 (by decide) (by decide), e 24#5 (by decide) (by decide),
      e 25#5 (by decide) (by decide), e 26#5 (by decide) (by decide),
      e 27#5 (by decide) (by decide), e 28#5 (by decide) (by decide),
      e 29#5 (by decide) (by decide), rfl⟩

theorem regL_callee' (L : List (BitVec 64)) (r : BitVec 5 → BitVec 64)
    (h : ∀ j, 19 ≤ j → j < 31 → L.getD j 0 = r (BitVec.ofNat 5 j)) :
    ∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 31 → regL L k = r k := by
  intro k hk hk'
  have := h k.toNat hk hk'
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

end X25519Dalek.Field
end

section
/-! # Limb arithmetic of `FieldElement51::pow2k`'s squaring step

`fe51_sq_poly_nat` is copied from DeepMind's `Shared51/Field51.lean` (google-deepmind/
code-verification @ 8c8d371f, Apache-2.0), with their `modPowLoop_eq`/`fpPow_eq_pow_mod` from
`Shared51/SliceBase.lean`; the doubling column follows their `fe51_sq_col128_nat`. -/

namespace X25519Dalek.Field

set_option maxRecDepth 20000

open Arm64

theorem tn_extr63 {v x y : BitVec 64} (h : v = BitVec.truncate 64 ((x ++ y) >>> 63)) :
    v.toNat = (x.toNat * 2 ^ 64 + y.toNat) / 2 ^ 63 % 2 ^ 64 := by
  subst h
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_append]
  have hy := y.isLt
  congr 2
  rw [← Nat.shiftLeft_add_eq_or_of_lt hy, Nat.shiftLeft_eq]

theorem tn_shl1 (x : BitVec 64) : (x <<< 1).toNat = x.toNat * 2 % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- A doubled column: `(H, L)` holds `X`; the code adds `2X` to a product `ph·2⁶⁴ + pl`. -/
theorem dbl_colB {H L E ph pl H' L' : BitVec 64} {X XB Pp PB : Nat}
    (hX : H.toNat * 2 ^ 64 + L.toNat = X) (hXb : X < XB) (hXB : XB ≤ 2 ^ 127)
    (eE : E = BitVec.truncate 64 ((H ++ L) >>> 63))
    (hp : ph.toNat * 2 ^ 64 + pl.toNat = Pp) (hpb : Pp < PB) (hB : PB + XB * 2 ≤ 2 ^ 128)
    (eL : L' = pl + L <<< 1)
    (eH : H' = (AddWithCarry64 E ph (AddWithCarry64 pl (L <<< 1) false).2.c).1) :
    H'.toNat * 2 ^ 64 + L'.toNat = Pp + X * 2 ∧ Pp + X * 2 < PB + XB * 2 := by
  have hE : E.toNat * 2 ^ 64 + (L <<< 1).toNat = X * 2 := by
    rw [tn_extr63 eE, tn_shl1, hX]
    have h2 : X * 2 < 2 ^ 64 * 2 ^ 64 := by
      calc X * 2 < XB * 2 := by omega
        _ ≤ 2 ^ 127 * 2 := by omega
        _ = 2 ^ 64 * 2 ^ 64 := by norm_num
    have h1 : X * 2 / 2 ^ 64 < 2 ^ 64 := (Nat.div_lt_iff_lt_mul (by norm_num)).2 h2
    have e1 : X / 2 ^ 63 = X * 2 / 2 ^ 64 := by
      rw [show (2 : Nat) ^ 64 = 2 ^ 63 * 2 by norm_num, Nat.mul_div_mul_right _ _ (by norm_num)]
    rw [e1, Nat.mod_eq_of_lt h1]
    have : L.toNat * 2 % 2 ^ 64 = X * 2 % 2 ^ 64 := by
      rw [← hX, Nat.add_mul, Nat.mul_right_comm, Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [this, Nat.mul_comm (X * 2 / 2 ^ 64)]
    exact Nat.div_add_mod (X * 2) (2 ^ 64)
  refine ⟨?_, by omega⟩
  rw [tn_adc eH, tn_add eL]
  have := acc_step (H := ph.toNat) (L := pl.toNat) (dH := E.toNat) (dL := (L <<< 1).toNat) hp hE
    pl.isLt (L <<< 1).isLt (by omega)
  rw [Nat.add_comm E.toNat ph.toNat]
  exact this

theorem fe51_sq_poly_nat (A0 A1 A2 A3 A4 : Nat) :
    ∃ K : Nat,
      ((A0 * A0 + (A1 * (A4 * 19) + A2 * (A3 * 19)) * 2) +
       ((A3 * 19) * A3 + (A0 * A1 + A2 * (A4 * 19)) * 2) * 2 ^ 51 +
       (A1 * A1 + (A0 * A2 + (A3 * 19) * A4) * 2) * 2 ^ 102 +
       ((A4 * 19) * A4 + (A0 * A3 + A1 * A2) * 2) * 2 ^ 153 +
       (A2 * A2 + (A0 * A4 + A1 * A3) * 2) * 2 ^ 204) + K * p25519 =
      (A0 + A1 * 2 ^ 51 + A2 * 2 ^ 102 + A3 * 2 ^ 153 + A4 * 2 ^ 204) *
      (A0 + A1 * 2 ^ 51 + A2 * 2 ^ 102 + A3 * 2 ^ 153 + A4 * 2 ^ 204) := by
  obtain ⟨K, h⟩ := fe51_mul_poly_nat A0 A1 A2 A3 A4 A0 A1 A2 A3 A4; refine ⟨K, ?_⟩; rw [← h]
  have c0 : A4 * (A1 * 19) = A1 * (A4 * 19) := by rw [← Nat.mul_assoc, Nat.mul_comm A4 A1, Nat.mul_assoc]
  have c1 : A3 * (A2 * 19) = A2 * (A3 * 19) := by rw [← Nat.mul_assoc, Nat.mul_comm A3 A2, Nat.mul_assoc]
  have c2 : A4 * (A2 * 19) = A2 * (A4 * 19) := by rw [← Nat.mul_assoc, Nat.mul_comm A4 A2, Nat.mul_assoc]
  have c3 : (A3 * 19) * A3 = A3 * (A3 * 19) := Nat.mul_comm _ _
  have c4 : A1 * A0 = A0 * A1 := Nat.mul_comm _ _; have c5 : A4 * (A3 * 19) = (A3 * 19) * A4 := Nat.mul_comm _ _
  have c6 : A3 * (A4 * 19) = (A3 * 19) * A4 := by rw [← Nat.mul_assoc, Nat.mul_right_comm A3 A4 19]
  have c7 : A2 * A0 = A0 * A2 := Nat.mul_comm _ _; have c8 : (A4 * 19) * A4 = A4 * (A4 * 19) := Nat.mul_comm _ _
  have c9 : A3 * A0 = A0 * A3 := Nat.mul_comm _ _; have c10 : A2 * A1 = A1 * A2 := Nat.mul_comm _ _
  have c11 : A4 * A0 = A0 * A4 := Nat.mul_comm _ _; have c12 : A3 * A1 = A1 * A3 := Nat.mul_comm _ _
  omega

theorem sq_arith {L0 L1 L2 L3 L4 : BitVec 64}
    {v40 v44 v48 v52 v56 v60 v64 v68 v72 v76 v80 v84 v88 v92 v96 v100 v104 v108 v112 v116 v120 v124 v128 v132 v136 v140 v144 v148 v152 v156 v160 v164 v168 v172 v176 v180 v184 v188 v192 v196 v200 v204 v208 v212 v216 v220 v224 v228 v232 v236 v240 v244 v248 v252 v256 v260 v264 v268 v272 v276 v280 v284 v288 v292 v296 v300 v304 v308 v312 v316 v320 v328 v332 v336 v340 v344 v348 v352 : BitVec 64}
    (e40 : v40 = L3 * 19#64)
    (e44 : v44 = L4 * 19#64)
    (e48 : v48 = L0 * L0)
    (e52 : v52 = L2 * v40)
    (e56 : v56 = L1 * v44)
    (e60 : v60 = mulhi L1 v44)
    (e64 : v64 = mulhi L2 v40)
    (e68 : v68 = v56 + v52)
    (e72 : v72 = mulhi L0 L0)
    (e76 : v76 = L0 * L1)
    (e80 : v80 = (AddWithCarry64 v60 v64 (AddWithCarry64 v56 v52 false).2.c).1)
    (e84 : v84 = v48 + v68 <<< 1)
    (e88 : v88 = L2 * v44)
    (e92 : v92 = BitVec.truncate 64 ((v80 ++ v68) >>> 63))
    (e96 : v96 = mulhi L0 L1)
    (e100 : v100 = (AddWithCarry64 v92 v72 (AddWithCarry64 v48 (v68 <<< 1) false).2.c).1)
    (e104 : v104 = BitVec.truncate 64 ((v100 ++ v84) >>> 51))
    (e108 : v108 = mulhi L2 v44)
    (e112 : v112 = v76 + v88)
    (e116 : v116 = v40 * L3)
    (e120 : v120 = mulhi v40 L3)
    (e124 : v124 = (AddWithCarry64 v96 v108 (AddWithCarry64 v76 v88 false).2.c).1)
    (e128 : v128 = L0 * L2)
    (e132 : v132 = BitVec.truncate 64 ((v124 ++ v112) >>> 63))
    (e136 : v136 = v116 + v112 <<< 1)
    (e140 : v140 = mulhi v40 L4)
    (e144 : v144 = (AddWithCarry64 v132 v120 (AddWithCarry64 v116 (v112 <<< 1) false).2.c).1)
    (e148 : v148 = v40 * L4)
    (e152 : v152 = mulhi L0 L2)
    (e156 : v156 = L1 * L1)
    (e160 : v160 = v128 + v148)
    (e164 : v164 = mulhi L1 L1)
    (e168 : v168 = (AddWithCarry64 v152 v140 (AddWithCarry64 v128 v148 false).2.c).1)
    (e172 : v172 = mulhi v44 L4)
    (e176 : v176 = BitVec.truncate 64 ((v168 ++ v160) >>> 63))
    (e180 : v180 = v156 + v160 <<< 1)
    (e184 : v184 = v44 * L4)
    (e188 : v188 = mulhi L0 L3)
    (e192 : v192 = mulhi L0 L4)
    (e196 : v196 = L0 * L4)
    (e200 : v200 = L0 * L3)
    (e204 : v204 = L1 * L2)
    (e208 : v208 = mulhi L1 L2)
    (e212 : v212 = mulhi L1 L3)
    (e216 : v216 = L1 * L3)
    (e220 : v220 = (AddWithCarry64 v176 v164 (AddWithCarry64 v156 (v160 <<< 1) false).2.c).1)
    (e224 : v224 = v200 + v204)
    (e228 : v228 = (AddWithCarry64 v188 v208 (AddWithCarry64 v200 v204 false).2.c).1)
    (e232 : v232 = L2 * L2)
    (e236 : v236 = BitVec.truncate 64 ((v228 ++ v224) >>> 63))
    (e240 : v240 = v184 + v224 <<< 1)
    (e244 : v244 = mulhi L2 L2)
    (e248 : v248 = (AddWithCarry64 v236 v172 (AddWithCarry64 v184 (v224 <<< 1) false).2.c).1)
    (e252 : v252 = v196 + v216)
    (e256 : v256 = (AddWithCarry64 v192 v212 (AddWithCarry64 v196 v216 false).2.c).1)
    (e260 : v260 = BitVec.truncate 64 ((v256 ++ v252) >>> 63))
    (e264 : v264 = v232 + v252 <<< 1)
    (e268 : v268 = (AddWithCarry64 v260 v244 (AddWithCarry64 v232 (v252 <<< 1) false).2.c).1)
    (e272 : v272 = v136 + v104)
    (e276 : v276 = if (AddWithCarry64 v136 v104 false).2.c = true then v144 + 1#64 else v144)
    (e280 : v280 = BitVec.truncate 64 ((v276 ++ v272) >>> 51))
    (e284 : v284 = v180 + v280)
    (e288 : v288 = if (AddWithCarry64 v180 v280 false).2.c = true then v220 + 1#64 else v220)
    (e292 : v292 = BitVec.truncate 64 ((v288 ++ v284) >>> 51))
    (e296 : v296 = v240 + v292)
    (e300 : v300 = if (AddWithCarry64 v240 v292 false).2.c = true then v248 + 1#64 else v248)
    (e304 : v304 = BitVec.truncate 64 ((v300 ++ v296) >>> 51))
    (e308 : v308 = v296 &&& 2251799813685247#64)
    (e312 : v312 = v264 + v304)
    (e316 : v316 = v84 &&& 2251799813685247#64)
    (e320 : v320 = if (AddWithCarry64 v264 v304 false).2.c = true then v268 + 1#64 else v268)
    (e328 : v328 = BitVec.truncate 64 ((v320 ++ v312) >>> 51))
    (e332 : v332 = v316 + v328 * 19#64)
    (e336 : v336 = v272 &&& 2251799813685247#64)
    (e340 : v340 = v284 &&& 2251799813685247#64)
    (e344 : v344 = v312 &&& 2251799813685247#64)
    (e348 : v348 = v336 + v332 >>> 51)
    (e352 : v352 = v332 &&& 2251799813685247#64)
    (hb : L0.toNat < 2 ^ 54 ∧ L1.toNat < 2 ^ 54 ∧ L2.toNat < 2 ^ 54 ∧ L3.toNat < 2 ^ 54 ∧
      L4.toNat < 2 ^ 54) :
    v352.toNat < 2 ^ 52 ∧ v348.toNat < 2 ^ 52 ∧ v340.toNat < 2 ^ 52 ∧ v308.toNat < 2 ^ 52 ∧
      v344.toNat < 2 ^ 52 ∧
      fe51Val v352 v348 v340 v308 v344 % p25519 =
        fe51Val L0 L1 L2 L3 L4 * fe51Val L0 L1 L2 L3 L4 % p25519 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hb
  have q3 := tn_mul19 e40 h3
  have q4 := tn_mul19 e44 h4
  have b19 : ∀ {x y : BitVec 64}, x.toNat < 2 ^ 54 → y.toNat < 2 ^ 54 →
      x.toNat * (y.toNat * 19) < 19 * 2 ^ 108 := fun hx hy => nat_mul_lt_19_108 hx (by omega)
  have b19' : ∀ {x y : BitVec 64}, x.toNat < 2 ^ 54 → y.toNat < 2 ^ 54 →
      (x.toNat * 19) * y.toNat < 19 * 2 ^ 108 := fun hx hy => by
        rw [Nat.mul_comm]; exact nat_mul_lt_19_108 hy (by omega)
  have b1 : ∀ {x y : BitVec 64}, x.toNat < 2 ^ 54 → y.toNat < 2 ^ 54 →
      x.toNat * y.toNat < 2 ^ 108 := fun hx hy => nat_mul_lt_108 hx hy
  -- column 0: L0² + 2(L1·19L4 + L2·19L3)
  have pa := prod_hl e60 e56
  have pb := prod_hl e64 e52
  have pc := prod_hl e72 e48
  rw [q4] at pa; rw [q3] at pb
  obtain ⟨x01, t01⟩ := col_stepB pa (b19 h1 h4) pb (b19 h2 h3) (by norm_num) e68 e80
  obtain ⟨s0, u0⟩ := dbl_colB x01 t01 (by norm_num) e92 pc (b1 h0 h0) (by norm_num) e84 e100
  have x0 := col_extractB s0 u0 (by norm_num) e104 e316
  -- column 1: 19L3·L3 + 2(L0L1 + L2·19L4)
  have pa1 := prod_hl e96 e76
  have pb1 := prod_hl e108 e88
  have pc1 := prod_hl e120 e116
  rw [q4] at pb1; rw [q3] at pc1
  obtain ⟨x11, t11⟩ := col_stepB pa1 (Nat.lt_of_lt_of_le (b1 h0 h1) (show 2 ^ 108 ≤ 19 * 2 ^ 108 by norm_num)) pb1 (b19 h2 h4)
    (by norm_num) e112 e124
  obtain ⟨s1, u1⟩ := dbl_colB x11 t11 (by norm_num) e132 pc1 (b19' h3 h3) (by norm_num) e136 e144
  obtain ⟨s1', u1'⟩ := col_cincB s1 u1 (by norm_num) e272 e276
  have x1 := col_extractB s1' u1' (by norm_num) e280 e336
  -- column 2: L1² + 2(L0L2 + 19L3·L4)
  have pa2 := prod_hl e152 e128
  have pb2 := prod_hl e140 e148
  have pc2 := prod_hl e164 e156
  rw [q3] at pb2
  obtain ⟨x21, t21⟩ := col_stepB pa2 (Nat.lt_of_lt_of_le (b1 h0 h2) (show 2 ^ 108 ≤ 19 * 2 ^ 108 by norm_num)) pb2 (b19' h3 h4)
    (by norm_num) e160 e168
  obtain ⟨s2, u2⟩ := dbl_colB x21 t21 (by norm_num) e176 pc2 (b1 h1 h1) (by norm_num) e180 e220
  obtain ⟨s2', u2'⟩ := col_cincB s2 u2 (by norm_num) e284 e288
  have x2 := col_extractB s2' u2' (by norm_num) e292 e340
  -- column 3: 19L4·L4 + 2(L0L3 + L1L2)
  have pa3 := prod_hl e188 e200
  have pb3 := prod_hl e208 e204
  have pc3 := prod_hl e172 e184
  rw [q4] at pc3
  obtain ⟨x31, t31⟩ := col_stepB pa3 (b1 h0 h3) pb3 (b1 h1 h2) (by norm_num) e224 e228
  obtain ⟨s3, u3⟩ := dbl_colB x31 t31 (by norm_num) e236 pc3 (b19' h4 h4) (by norm_num) e240 e248
  obtain ⟨s3', u3'⟩ := col_cincB s3 u3 (by norm_num) e296 e300
  have x3 := col_extractB s3' u3' (by norm_num) e304 e308
  -- column 4: L2² + 2(L0L4 + L1L3)
  have pa4 := prod_hl e192 e196
  have pb4 := prod_hl e212 e216
  have pc4 := prod_hl e244 e232
  obtain ⟨x41, t41⟩ := col_stepB pa4 (b1 h0 h4) pb4 (b1 h1 h3) (by norm_num) e252 e256
  obtain ⟨s4, u4⟩ := dbl_colB x41 t41 (by norm_num) e260 pc4 (b1 h2 h2) (by norm_num) e264 e268
  obtain ⟨s4', u4'⟩ := col_cincB s4 u4 (by norm_num) e312 e320
  have x4 := col_extractB s4' u4' (by norm_num) e328 e344
  have hc4 := c4_bound x4 (lt_of_lt_le' u4 (by norm_num)) v304.isLt
  obtain ⟨hd0, hr1⟩ := mul_final_carry x0.2 x1.2 hc4 e332 e352 e348
  obtain ⟨r0b, r1b, r2b, r3b, r4b, hcar⟩ := fe51_mul_carry_nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (lt_of_lt_le' u0 (by norm_num)) (lt_of_lt_le' u1 (by norm_num))
    (lt_of_lt_le' u2 (by norm_num)) (lt_of_lt_le' u3 (by norm_num))
    (lt_of_lt_le' u4 (by norm_num)) x0 x1 x2 x3 x4 hd0 hr1
  obtain ⟨K, hpoly⟩ := fe51_sq_poly_nat L0.toNat L1.toNat L2.toNat L3.toNat L4.toNat
  refine ⟨r0b, r1b, r2b, r3b, r4b, ?_⟩
  unfold fe51Val
  have htot : (v352.toNat + v348.toNat * 2 ^ 51 + v340.toNat * 2 ^ 102 + v308.toNat * 2 ^ 153 +
      v344.toNat * 2 ^ 204) + (v328.toNat + K) * p25519 =
      (L0.toNat + L1.toNat * 2 ^ 51 + L2.toNat * 2 ^ 102 + L3.toNat * 2 ^ 153 + L4.toNat * 2 ^ 204) *
      (L0.toNat + L1.toNat * 2 ^ 51 + L2.toNat * 2 ^ 102 + L3.toNat * 2 ^ 153 + L4.toNat * 2 ^ 204) := by
    rw [Nat.add_mul, ← Nat.add_assoc, hcar]; exact hpoly
  rw [← htot, Nat.add_mul_mod_self_right]

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

theorem inCells_rw (bs : List (BitVec 8)) (a : BitVec 64) : InCells (a ↦ₛ bs) a bs HeapCell.rw :=
  fun h hh i hi => rwCells_bytes bs a h hh i hi

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
/-! # `<&FieldElement51 as Mul>::mul` (block 1, 166 instructions): the run -/

namespace X25519Dalek.Field

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Arm64 Arm64.Obj


section fetch
variable {mpl : MultiPlacement} {m : Memory} (hCL : (prog mpl 1).CodeLoaded m)
include hCL

end fetch

end X25519Dalek.Field
end

section
/-! # `<&FieldElement51 as Mul>::mul`: the three contracts -/

namespace X25519Dalek.Field

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

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

end X25519Dalek.Field
end

section
/-! # `FieldElement51::pow2k` (block 2): fetches and one iteration of the squaring loop -/

namespace X25519Dalek.Field

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Arm64 Arm64.Obj

theorem blk02 : x25519CliBlocks.getD 2 { code := [] } = x25519CliBlk02 := rfl

section fetch
variable {mpl : MultiPlacement} {m : Memory} (hCL : (prog mpl 2).CodeLoaded m)
include hCL

theorem f02_0 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 0) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.sp) 0xffffffffffffffa0#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_4 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 4) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x1b#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_8 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 8) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x19#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000020#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_12 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 12) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x17#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000030#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_16 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 16) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000040#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_20 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 20) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000050#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_24 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 24) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_28 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 28) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x09#5) 0x0013#16 0) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_32 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 32) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000010#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_36 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 36) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x0e#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000020#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_40 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 40) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_44 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 44) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_48 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 48) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_52 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 52) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_56 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 56) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_60 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 60) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_64 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 64) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_68 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 68) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x04#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_72 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 72) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_76 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 76) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_80 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 80) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x03#5)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_84 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 84) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 1) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_88 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 88) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x15#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_92 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 92) =
    some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) 63) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_96 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 96) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_100 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 100) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x11#5)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_104 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 104) =
    some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x12#5) 51) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_108 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 108) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_112 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 112) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.gpr 0x15#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_116 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 116) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_120 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 120) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_124 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 124) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x07#5) (Arm64.Reg.gpr 0x14#5)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_128 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 128) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_132 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 132) =
    some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x00#5) 63) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_136 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 136) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 1) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_140 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 140) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_144 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 144) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x05#5)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_148 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 148) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_152 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 152) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_156 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 156) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x17#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_160 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 160) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x19#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_164 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 164) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_168 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 168) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x1a#5)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_172 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 172) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x1b#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_176 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 176) =
    some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x0f#5) 63) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_180 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 180) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x17#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.ShiftType.LSL) 1) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_184 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 184) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_188 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 188) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_192 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 192) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x1e#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_196 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 196) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_200 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 200) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_204 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 204) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_208 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 208) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_212 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 212) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x06#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_216 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 216) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_220 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 220) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x16#5)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_224 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 224) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x04#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_228 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 228) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x03#5)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_232 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 232) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_236 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 236) =
    some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x0d#5) 63) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_240 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 240) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.ShiftType.LSL) 1) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_244 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 244) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.UMULH) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.xzr)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_248 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 248) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x1b#5)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_252 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 252) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_256 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 256) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.Reg.gpr 0x06#5)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_260 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 260) =
    some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0b#5) 63) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_264 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 264) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 1) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_268 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 268) =
    some (Arm64.Instr.addSubCarry (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0a#5)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_272 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 272) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x11#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_276 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 276) =
    some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINC) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) (Arm64.CondCode.CC)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_280 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 280) =
    some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x11#5) (Arm64.Reg.gpr 0x0e#5) 51) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_284 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 284) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x0f#5) (Arm64.Reg.gpr 0x11#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_288 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 288) =
    some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINC) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.CondCode.CC)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_292 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 292) =
    some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0f#5) 51) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_296 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 296) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_300 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 300) =
    some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINC) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x10#5) (Arm64.CondCode.CC)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_304 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 304) =
    some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0c#5) 51) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_308 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 308) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) 0x0007ffffffffffff#64) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_312 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 312) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADDS) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_316 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 316) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x12#5) 0x0007ffffffffffff#64) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_320 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 320) =
    some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSINC) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.CondCode.CC)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_324 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 324) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W32) (Arm64.AddSubOp.SUBS) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x01#5) 0x001#12 false) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_328 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 328) =
    some (Arm64.Instr.extr (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0d#5) 51) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_332 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 332) =
    some (Arm64.Instr.dataProc3 (Arm64.RegWidth.W64) (Arm64.DataProc3Op.MADD) (Arm64.Reg.gpr 0x10#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0b#5)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_336 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 336) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0e#5) 0x0007ffffffffffff#64) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_340 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 340) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0f#5) 0x0007ffffffffffff#64) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_344 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 344) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0e#5) (Arm64.Reg.gpr 0x0d#5) 0x0007ffffffffffff#64) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_348 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 348) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x10#5) (Arm64.ShiftType.LSR) 51) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_352 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 352) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x10#5) 0x0007ffffffffffff#64) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_356 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 356) =
    some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0xfffffffffffffec4#64) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_360 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 360) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000050#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_364 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 364) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x08#5) 0x0000000000000000#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_368 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 368) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000040#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_372 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 372) =
    some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x08#5) 0x0000000000000010#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_376 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 376) =
    some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0e#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x08#5) 0x0000000000000020#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_380 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 380) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x18#5) (Arm64.Reg.gpr 0x17#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000030#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_384 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 384) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1a#5) (Arm64.Reg.gpr 0x19#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000020#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_388 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 388) =
    some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1c#5) (Arm64.Reg.gpr 0x1b#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_392 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 392) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.sp) 0x0000000000000060#64)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f02_396 : rawFetch m (mpl.base 2 + BitVec.ofNat 64 396) =
    some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) :=
  fetch_plain blk02 (by decide) hCL (by decide) (by decide) rfl rfl

end fetch

theorem p2k_body {mpl : MultiPlacement} {P : State → Prop} {s : State} {pcb : BitVec 64}
    {sp : BitVec 64} {m m0 : Memory} {ps : PState} {W : BitVec 64 → Prop}
    {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : BitVec 64}
    (hCL : (prog mpl 2).CodeLoaded m0) (hpcb : pcb = mpl.base 2)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hb : y13.toNat < 2 ^ 54 ∧ y11.toNat < 2 ^ 54 ∧ y10.toNat < 2 ^ 54 ∧ y12.toNat < 2 ^ 54 ∧
      y14.toNat < 2 ^ 54)
    (h9 : y9 = 19#64)
    (hP : ∀ (L : List (BitVec 64)) (ps' : PState) (l0 l1 l2 l3 l4 : BitVec 64),
      L.length = 32 → L.getD 8 0 = y8 → L.getD 29 0 = y29 → L.getD 9 0 = 19#64 →
      L.getD 13 0 = l0 → L.getD 11 0 = l1 → L.getD 10 0 = l2 → L.getD 12 0 = l3 → L.getD 14 0 = l4 →
      L.getD 1 0 = (BitVec.truncate 32 y1 - 1#32).zeroExtend 64 →
      ps'.z = decide (BitVec.truncate 32 y1 - 1#32 = 0#32) →
      l0.toNat < 2 ^ 52 → l1.toNat < 2 ^ 52 → l2.toNat < 2 ^ 52 → l3.toNat < 2 ^ 52 →
      l4.toNat < 2 ^ 52 →
      fe51Val l0 l1 l2 l3 l4 % p25519 =
        fe51Val y13 y11 y10 y12 y14 * fe51Val y13 y11 y10 y12 y14 % p25519 →
      Reach mpl 2 P (mkS s (pcb + BitVec.ofNat 64 356) (regL L) sp m ps')) :
    Reach mpl 2 P (mkS s (pcb + BitVec.ofNat 64 40) (regL [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y29, y30, y31]) sp m ps) := by
  subst h9 hpcb
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_40 hCL) (fun v40 e40 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e40 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_44 hCL) (fun v44 e44 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e44 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_48 hCL) (fun v48 e48 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e48 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_52 hCL) (fun v52 e52 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e52 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_56 hCL) (fun v56 e56 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e56 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f02_60 hCL) (fun v60 e60 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e60 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f02_64 hCL) (fun v64 e64 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e64 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f02_68 hCL) (fun v68 e68 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e68 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f02_72 hCL) (fun v72 e72 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e72 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_76 hCL) (fun v76 e76 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e76 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f02_80 hCL) (fun v80 e80 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e80 ⊢
  refine r_adds_lsl (by decide) (by decide) (by decide) hrun hW hok (f02_84 hCL) (fun v84 e84 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e84 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_88 hCL) (fun v88 e88 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e88 ⊢
  refine r_extr (by decide) (by decide) (by decide) hrun hW hok (f02_92 hCL) (fun v92 e92 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e92 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f02_96 hCL) (fun v96 e96 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e96 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f02_100 hCL) (fun v100 e100 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e100 ⊢
  refine r_extr (by decide) (by decide) (by decide) hrun hW hok (f02_104 hCL) (fun v104 e104 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e104 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f02_108 hCL) (fun v108 e108 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e108 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f02_112 hCL) (fun v112 e112 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e112 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_116 hCL) (fun v116 e116 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e116 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f02_120 hCL) (fun v120 e120 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e120 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f02_124 hCL) (fun v124 e124 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e124 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_128 hCL) (fun v128 e128 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e128 ⊢
  refine r_extr (by decide) (by decide) (by decide) hrun hW hok (f02_132 hCL) (fun v132 e132 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e132 ⊢
  refine r_adds_lsl (by decide) (by decide) (by decide) hrun hW hok (f02_136 hCL) (fun v136 e136 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e136 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f02_140 hCL) (fun v140 e140 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e140 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f02_144 hCL) (fun v144 e144 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e144 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_148 hCL) (fun v148 e148 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e148 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f02_152 hCL) (fun v152 e152 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e152 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_156 hCL) (fun v156 e156 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e156 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f02_160 hCL) (fun v160 e160 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e160 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f02_164 hCL) (fun v164 e164 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e164 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f02_168 hCL) (fun v168 e168 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e168 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f02_172 hCL) (fun v172 e172 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e172 ⊢
  refine r_extr (by decide) (by decide) (by decide) hrun hW hok (f02_176 hCL) (fun v176 e176 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e176 ⊢
  refine r_adds_lsl (by decide) (by decide) (by decide) hrun hW hok (f02_180 hCL) (fun v180 e180 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e180 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_184 hCL) (fun v184 e184 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e184 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f02_188 hCL) (fun v188 e188 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e188 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f02_192 hCL) (fun v192 e192 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e192 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_196 hCL) (fun v196 e196 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e196 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_200 hCL) (fun v200 e200 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e200 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_204 hCL) (fun v204 e204 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e204 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f02_208 hCL) (fun v208 e208 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e208 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f02_212 hCL) (fun v212 e212 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e212 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_216 hCL) (fun v216 e216 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e216 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f02_220 hCL) (fun v220 e220 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e220 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f02_224 hCL) (fun v224 e224 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e224 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f02_228 hCL) (fun v228 e228 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e228 ⊢
  refine r_mul (by decide) (by decide) (by decide) hrun hW hok (f02_232 hCL) (fun v232 e232 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e232 ⊢
  refine r_extr (by decide) (by decide) (by decide) hrun hW hok (f02_236 hCL) (fun v236 e236 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e236 ⊢
  refine r_adds_lsl (by decide) (by decide) (by decide) hrun hW hok (f02_240 hCL) (fun v240 e240 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e240 ⊢
  refine r_umulh (by decide) (by decide) (by decide) hrun hW hok (f02_244 hCL) (fun v244 e244 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e244 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f02_248 hCL) (fun v248 e248 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e248 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f02_252 hCL) (fun v252 e252 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e252 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f02_256 hCL) (fun v256 e256 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e256 ⊢
  refine r_extr (by decide) (by decide) (by decide) hrun hW hok (f02_260 hCL) (fun v260 e260 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e260 ⊢
  refine r_adds_lsl (by decide) (by decide) (by decide) hrun hW hok (f02_264 hCL) (fun v264 e264 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e264 ⊢
  refine r_adc (by decide) (by decide) (by decide) hrun hW hok (f02_268 hCL) (fun v268 e268 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e268 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f02_272 hCL) (fun v272 e272 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e272 ⊢
  refine r_cinc (by decide) (by decide) hrun hW hok (f02_276 hCL) (fun v276 e276 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e276 ⊢
  refine r_extr (by decide) (by decide) (by decide) hrun hW hok (f02_280 hCL) (fun v280 e280 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e280 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f02_284 hCL) (fun v284 e284 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e284 ⊢
  refine r_cinc (by decide) (by decide) hrun hW hok (f02_288 hCL) (fun v288 e288 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e288 ⊢
  refine r_extr (by decide) (by decide) (by decide) hrun hW hok (f02_292 hCL) (fun v292 e292 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e292 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f02_296 hCL) (fun v296 e296 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e296 ⊢
  refine r_cinc (by decide) (by decide) hrun hW hok (f02_300 hCL) (fun v300 e300 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e300 ⊢
  refine r_extr (by decide) (by decide) (by decide) hrun hW hok (f02_304 hCL) (fun v304 e304 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e304 ⊢
  refine r_andi (by decide) (by decide) hrun hW hok (f02_308 hCL) (fun v308 e308 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e308 ⊢
  refine r_adds (by decide) (by decide) (by decide) hrun hW hok (f02_312 hCL) (fun v312 e312 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e312 ⊢
  refine r_andi (by decide) (by decide) hrun hW hok (f02_316 hCL) (fun v316 e316 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e316 ⊢
  refine r_cinc (by decide) (by decide) hrun hW hok (f02_320 hCL) (fun v320 e320 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e320 ⊢
  refine r_subs1 (by decide) (by decide) hrun hW hok (f02_324 hCL) (fun v324 psz e324 hz => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e324 ⊢
  refine r_extr (by decide) (by decide) (by decide) hrun hW hok (f02_328 hCL) (fun v328 e328 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e328 ⊢
  refine r_madd (by decide) (by decide) (by decide) (by decide) hrun hW hok (f02_332 hCL) (fun v332 e332 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e332 ⊢
  refine r_andi (by decide) (by decide) hrun hW hok (f02_336 hCL) (fun v336 e336 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e336 ⊢
  refine r_andi (by decide) (by decide) hrun hW hok (f02_340 hCL) (fun v340 e340 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e340 ⊢
  refine r_andi (by decide) (by decide) hrun hW hok (f02_344 hCL) (fun v344 e344 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e344 ⊢
  refine r_add_lsr (by decide) (by decide) (by decide) hrun hW hok (f02_348 hCL) (fun v348 e348 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e348 ⊢
  refine r_andi (by decide) (by decide) hrun hW hok (f02_352 hCL) (fun v352 e352 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e352 ⊢
  subst v324
  obtain ⟨r0b, r1b, r2b, r3b, r4b, hval⟩ := sq_arith e40 e44 e48 e52 e56 e60 e64 e68 e72 e76 e80 e84 e88 e92 e96 e100 e104 e108 e112 e116 e120 e124 e128 e132 e136 e140 e144 e148 e152 e156 e160 e164 e168 e172 e176 e180 e184 e188 e192 e196 e200 e204 e208 e212 e216 e220 e224 e228 e232 e236 e240 e244 e248 e252 e256 e260 e264 e268 e272 e276 e280 e284 e288 e292 e296 e300 e304 e308 e312 e316 e320 e328 e332 e336 e340 e344 e348 e352 hb
  exact hP _ _ v352 v348 v340 v308 v344 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hz r0b r1b r2b r3b r4b hval

end X25519Dalek.Field
end

section
/-! # `FieldElement51::pow2k`: the squaring loop, by induction on the counter -/

namespace X25519Dalek.Field

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

theorem getD_eq_get (L : List (BitVec 64)) (i : Nat) (h : i < L.length) : L.getD i 0 = L[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem list32_eta (L : List (BitVec 64)) (hL : L.length = 32) :
    L = [L.getD 0 0, L.getD 1 0, L.getD 2 0, L.getD 3 0, L.getD 4 0, L.getD 5 0, L.getD 6 0,
      L.getD 7 0, L.getD 8 0, L.getD 9 0, L.getD 10 0, L.getD 11 0, L.getD 12 0, L.getD 13 0,
      L.getD 14 0, L.getD 15 0, L.getD 16 0, L.getD 17 0, L.getD 18 0, L.getD 19 0, L.getD 20 0,
      L.getD 21 0, L.getD 22 0, L.getD 23 0, L.getD 24 0, L.getD 25 0, L.getD 26 0, L.getD 27 0,
      L.getD 28 0, L.getD 29 0, L.getD 30 0, L.getD 31 0] := by
  apply List.ext_getElem (by simp [hL])
  intro i h1 h2
  rw [hL] at h1
  interval_cases i <;> exact (getD_eq_get L _ (by omega)).symm

theorem trunc_sub1 (y : BitVec 64) (n : Nat) (hy : BitVec.truncate 32 y = BitVec.ofNat 32 (n + 1))
    (hn : n + 1 < 2 ^ 32) :
    BitVec.truncate 32 ((BitVec.truncate 32 y - 1#32).zeroExtend 64) = BitVec.ofNat 32 n := by
  rw [hy]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem sub1_zero_iff (y : BitVec 64) (n : Nat) (hy : BitVec.truncate 32 y = BitVec.ofNat 32 (n + 1))
    (hn : n + 1 < 2 ^ 32) : (BitVec.truncate 32 y - 1#32 = 0#32) ↔ n = 0 := by
  rw [hy]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    omega
  · intro h; subst h; rfl

theorem pc356_40 (b : BitVec 64) :
    b + BitVec.ofNat 64 356 + 0xfffffffffffffec4#64 = b + BitVec.ofNat 64 40 := by
  rw [BitVec.add_assoc]; rfl

theorem p2k_loop {mpl : MultiPlacement} {P : State → Prop} {s : State} {pcb sp : BitVec 64}
    {m m0 : Memory} {W : BitVec 64 → Prop}
    (hCL : (prog mpl 2).CodeLoaded m0) (hpcb : pcb = mpl.base 2)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m) :
    ∀ n : Nat, 1 ≤ n → n < 2 ^ 32 → ∀ (L : List (BitVec 64)) (ps : PState), L.length = 32 →
      BitVec.truncate 32 (L.getD 1 0) = BitVec.ofNat 32 n → L.getD 9 0 = 19#64 →
      ((L.getD 13 0).toNat < 2 ^ 54 ∧ (L.getD 11 0).toNat < 2 ^ 54 ∧ (L.getD 10 0).toNat < 2 ^ 54 ∧
        (L.getD 12 0).toNat < 2 ^ 54 ∧ (L.getD 14 0).toNat < 2 ^ 54) →
      (∀ (L' : List (BitVec 64)) (ps' : PState) (l0 l1 l2 l3 l4 : BitVec 64),
        L'.length = 32 → L'.getD 8 0 = L.getD 8 0 → L'.getD 29 0 = L.getD 29 0 →
        L'.getD 13 0 = l0 → L'.getD 11 0 = l1 → L'.getD 10 0 = l2 → L'.getD 12 0 = l3 →
        L'.getD 14 0 = l4 →
        l0.toNat < 2 ^ 52 → l1.toNat < 2 ^ 52 → l2.toNat < 2 ^ 52 → l3.toNat < 2 ^ 52 →
        l4.toNat < 2 ^ 52 →
        fe51Val l0 l1 l2 l3 l4 % p25519 =
          (fe51Val (L.getD 13 0) (L.getD 11 0) (L.getD 10 0) (L.getD 12 0) (L.getD 14 0)) ^ (2 ^ n) %
            p25519 →
        Reach mpl 2 P (mkS s (pcb + BitVec.ofNat 64 360) (regL L') sp m ps')) →
      Reach mpl 2 P (mkS s (pcb + BitVec.ofNat 64 40) (regL L) sp m ps) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro _ hn L ps hL hc h9 hb hP
    rw [list32_eta L hL]
    refine p2k_body hCL hpcb hrun hW hok hb h9 ?_
    intro L' ps' l0 l1 l2 l3 l4 hL' h8 h29 h9' e0 e1 e2 e3 e4 hc' hz b0 b1 b2 b3 b4 hval
    subst hpcb
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hz' : ps'.z = true := by
        have := (sub1_zero_iff _ 0 hc hn).2 rfl; rw [hz]; exact decide_eq_true this
      refine r_bne_not hz' hrun hW hok (f02_356 hCL) ?_
      refine hP L' ps' l0 l1 l2 l3 l4 hL' h8 h29 e0 e1 e2 e3 e4 b0 b1 b2 b3 b4 ?_
      rw [hval]; simp [pow_two]
    · have hz' : ps'.z = false := by
        rw [hz]; simp only [decide_eq_false_iff_not]; rw [sub1_zero_iff _ k hc hn]; omega
      refine r_bne_taken hz' hrun hW hok (f02_356 hCL) (pc356_40 _) ?_
      refine ih hk (by omega) L' ps' hL' ?_ h9' ⟨?_, ?_, ?_, ?_, ?_⟩ ?_
      · rw [hc']; exact trunc_sub1 _ k hc hn
      · rw [e0]; omega
      · rw [e1]; omega
      · rw [e2]; omega
      · rw [e3]; omega
      · rw [e4]; omega
      · intro L'' ps'' m0' m1' m2' m3' m4' hL'' h8' h29' f0 f1 f2 f3 f4 c0 c1 c2 c3 c4 hv
        refine hP L'' ps'' m0' m1' m2' m3' m4' hL'' (h8'.trans h8) (h29'.trans h29) f0 f1 f2 f3 f4
          c0 c1 c2 c3 c4 ?_
        rw [hv, e0, e1, e2, e3, e4, Nat.pow_mod, hval, ← Nat.pow_mod, ← pow_two, ← pow_mul,
          ← pow_succ']

end X25519Dalek.Field
end

section
/-! # `FieldElement51::pow2k` (block 2): prologue, loop, epilogue -/

namespace X25519Dalek.Field

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Arm64 Arm64.Obj

theorem p2k_run {mpl : MultiPlacement} {P : State → Prop} {s0 : State} {W : BitVec 64 → Prop}
    {a out A0 A1 A2 A3 A4 : BitVec 64} {k : Nat}
    (hCL : (prog mpl 2).CodeLoaded s0.mem)
    (hrun : s0.status = .Running) (hW : WOwned s0.mem W) (hsp : s0.sp.toNat % 16 = 0)
    (hsp' : (s0.sp + 0xffffffffffffffa0#64).toNat % 16 = 0)
    (hstk : ∀ x : BitVec 64, (x - (s0.sp - 96#64)).toNat + 8 ≤ 96 → AllB W x 8)
    (hout : ∀ c : BitVec 64, c.toNat + 8 ≤ 40 → AllB W (out + c) 8)
    (hout2 : ∀ c : BitVec 64, c.toNat + 16 ≤ 40 → AllB W (out + c + 8#64) 8)
    (hfar : ∀ c c' : BitVec 64, c.toNat + 8 ≤ 40 → (c' + 96#64).toNat + 8 ≤ 96 →
      Far (out + c) (s0.sp + c'))
    (hfar0 : ∀ c' : BitVec 64, (c' + 96#64).toNat + 8 ≤ 96 → Far out (s0.sp + c'))
    (hrA : ∀ m c, MemOK s0.mem W m → c.toNat + 8 ≤ 40 → m.canRead (a + c) 8 = true)
    (hrA2 : ∀ m c, MemOK s0.mem W m → c.toNat + 16 ≤ 40 → m.canRead (a + c + 8#64) 8 = true)
    (hA0 : ∀ m, MemOK s0.mem W m → m.read64 a = A0)
    (hA1 : ∀ m, MemOK s0.mem W m → m.read64 (a + 8#64) = A1)
    (hA2 : ∀ m, MemOK s0.mem W m → m.read64 (a + 16#64) = A2)
    (hA3 : ∀ m, MemOK s0.mem W m → m.read64 (a + 24#64) = A3)
    (hA4 : ∀ m, MemOK s0.mem W m → m.read64 (a + 32#64) = A4)
    (hbA : A0.toNat < 2 ^ 54 ∧ A1.toNat < 2 ^ 54 ∧ A2.toNat < 2 ^ 54 ∧ A3.toNat < 2 ^ 54 ∧
      A4.toNat < 2 ^ 54)
    (ha : s0.regs.regs 0#5 = a) (ho : s0.regs.regs 8#5 = out)
    (hk : BitVec.truncate 32 (s0.regs.regs 1#5) = BitVec.ofNat 32 k) (hk1 : 1 ≤ k) (hk2 : k < 256)
    (hP : ∀ (L : List (BitVec 64)) (m : Memory) (ps : PState) (l0 l1 l2 l3 l4 : BitVec 64),
      (∀ k : BitVec 5, 19 ≤ k.toNat → k.toNat < 31 → regL L k = s0.regs.regs k) →
      MemOK s0.mem W m →
      m.read64 out = l0 → m.read64 (out + 8#64) = l1 → m.read64 (out + 16#64) = l2 →
      m.read64 (out + 24#64) = l3 → m.read64 (out + 32#64) = l4 →
      l0.toNat < 2 ^ 52 → l1.toNat < 2 ^ 52 → l2.toNat < 2 ^ 52 → l3.toNat < 2 ^ 52 →
      l4.toNat < 2 ^ 52 →
      fe51Val l0 l1 l2 l3 l4 % p25519 = (fe51Val A0 A1 A2 A3 A4) ^ (2 ^ k) % p25519 →
      P (mkS s0 (s0.regs.regs 30#5) (regL L) s0.sp m ps)) :
    Reach mpl 2 P (mkS s0 (mpl.base 2 + BitVec.ofNat 64 0) (regL [s0.regs.regs 0#5, s0.regs.regs 1#5, s0.regs.regs 2#5, s0.regs.regs 3#5, s0.regs.regs 4#5, s0.regs.regs 5#5, s0.regs.regs 6#5, s0.regs.regs 7#5, s0.regs.regs 8#5, s0.regs.regs 9#5, s0.regs.regs 10#5, s0.regs.regs 11#5, s0.regs.regs 12#5, s0.regs.regs 13#5, s0.regs.regs 14#5, s0.regs.regs 15#5, s0.regs.regs 16#5, s0.regs.regs 17#5, s0.regs.regs 18#5, s0.regs.regs 19#5, s0.regs.regs 20#5, s0.regs.regs 21#5, s0.regs.regs 22#5, s0.regs.regs 23#5, s0.regs.regs 24#5, s0.regs.regs 25#5, s0.regs.regs 26#5, s0.regs.regs 27#5, s0.regs.regs 28#5, s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 31#5]) s0.sp s0.mem
      s0.pstate) := by
  rw [ha, ho]
  have hok := memOK_refl s0.mem W
  refine r_str_pre_sp (by decide) hsp hrun hW hok (f02_0 hCL) (hstk _ (by bv_omega)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f02_4 hCL) (hstk _ (by bv_omega)) (hstk _ (by bv_omega)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f02_8 hCL) (hstk _ (by bv_omega)) (hstk _ (by bv_omega)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f02_12 hCL) (hstk _ (by bv_omega)) (hstk _ (by bv_omega)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f02_16 hCL) (hstk _ (by bv_omega)) (hstk _ (by bv_omega)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_stp_sp (by decide) (by decide) hsp' hrun hW hok (f02_20 hCL) (hstk _ (by bv_omega)) (hstk _ (by bv_omega)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_ldp_g (by decide) (by decide) (by decide) hrun hW hok (f02_24 hCL) (hrA _ _ hok (by decide)) (hrA2 _ _ hok (by decide)) (fun v24a v24b e24a e24b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e24a e24b ⊢
  rw [hA0 _ hok] at e24a; rw [hA1 _ hok] at e24b; subst v24a v24b
  refine r_movz (by decide) hrun hW hok (f02_28 hCL) ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13]
  refine r_ldp_g (by decide) (by decide) (by decide) hrun hW hok (f02_32 hCL) (hrA _ _ hok (by decide)) (hrA2 _ _ hok (by decide)) (fun v32a v32b e32a e32b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e32a e32b ⊢
  rw [hA2 _ hok] at e32a; rw [hA3 _ hok] at e32b; subst v32a v32b
  refine r_ldr_g (by decide) (by decide) hrun hW hok (f02_36 hCL) (hrA _ _ hok (by decide)) (fun v36 e36 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at e36 ⊢
  rw [hA4 _ hok] at e36; subst v36
  refine p2k_loop hCL rfl hrun hW hok k hk1 (by omega) _ _ rfl (by simpa using hk) rfl hbA ?_
  intro L' ps' l0 l1 l2 l3 l4 hlen h8 h29 e0 e1 e2 e3 e4 b0 b1 b2 b3 b4 hval
  rw [list32_eta L' hlen]
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h8 h29
  rw [h8, h29, e0, e1, e2, e3, e4]
  refine r_ldp_sp (by decide) (by decide) hsp' hrun hW hok (f02_360 hCL) (canRead_of_W hW hok (hstk _ (by bv_omega))) (canRead_of_W hW hok (hstk _ (by bv_omega))) (fun v360a v360b e360a e360b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hfar, hfar0] at e360a e360b ⊢
  subst v360a v360b
  refine r_stp_g (by decide) (by decide) (by decide) hrun hW hok (f02_364 hCL) (hout _ (by decide)) (hout2 _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_ldp_sp (by decide) (by decide) hsp' hrun hW hok (f02_368 hCL) (canRead_of_W hW hok (hstk _ (by bv_omega))) (canRead_of_W hW hok (hstk _ (by bv_omega))) (fun v368a v368b e368a e368b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hfar, hfar0] at e368a e368b ⊢
  subst v368a v368b
  refine r_stp_g (by decide) (by decide) (by decide) hrun hW hok (f02_372 hCL) (hout _ (by decide)) (hout2 _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_str_g (by decide) (by decide) hrun hW hok (f02_376 hCL) (hout _ (by decide)) (fun hok => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13] at hok ⊢
  refine r_ldp_sp (by decide) (by decide) hsp' hrun hW hok (f02_380 hCL) (canRead_of_W hW hok (hstk _ (by bv_omega))) (canRead_of_W hW hok (hstk _ (by bv_omega))) (fun v380a v380b e380a e380b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hfar, hfar0] at e380a e380b ⊢
  subst v380a v380b
  refine r_ldp_sp (by decide) (by decide) hsp' hrun hW hok (f02_384 hCL) (canRead_of_W hW hok (hstk _ (by bv_omega))) (canRead_of_W hW hok (hstk _ (by bv_omega))) (fun v384a v384b e384a e384b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hfar, hfar0] at e384a e384b ⊢
  subst v384a v384b
  refine r_ldp_sp (by decide) (by decide) hsp' hrun hW hok (f02_388 hCL) (canRead_of_W hW hok (hstk _ (by bv_omega))) (canRead_of_W hW hok (hstk _ (by bv_omega))) (fun v388a v388b e388a e388b => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hfar, hfar0] at e388a e388b ⊢
  subst v388a v388b
  refine r_ldr_post_sp (by decide) hsp' hrun hW hok (f02_392 hCL) (canRead_of_W hW hok (hstk _ (by bv_omega))) (fun v392 e392 => ?_)
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ze_e0, ze_13, read64_write64_far, read64_write64_same, far_add_iff, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceLeDiff, and_self, Nat.reduceMod, Nat.reducePow, hfar, hfar0] at e392 ⊢
  subst v392
  refine r_ret hrun hW hok (f02_396 hCL) ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ,
    List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod,
    Nat.reducePow, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
  refine hP _ _ _ l0 l1 l2 l3 l4
    (regL_callee' _ _ (fun j h1 h2 => by interval_cases j <;> rfl)) hok ?_ ?_ ?_ ?_ ?_
    b0 b1 b2 b3 b4 hval
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
/-! # `FieldElement51::pow2k`: the contract

`modPowLoop_eq` and `modPow_mod_eq_pow_mod` are copied from DeepMind's `Shared51/SliceBase.lean`
(google-deepmind/code-verification @ 8c8d371f, Apache-2.0). -/

namespace X25519Dalek.Field

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

theorem beq_false_of_ne' {a b : Nat} (h : a ≠ b) : (a == b) = false :=
  beq_false_of_ne h

theorem modPowLoop_eq (fuel : Nat) :
    ∀ (base exp m acc : Nat), exp < 2 ^ fuel → modPowLoop fuel base exp m acc = (acc * base ^ exp) % m := by
  induction fuel with
  | zero => intro base exp m acc hexp; (have h0 : exp = 0 := by omega); subst h0; simp [modPowLoop]
  | succ fuel ih =>
    intro base exp m acc hexp; unfold modPowLoop
    by_cases h0 : exp = 0
    · subst h0; simp
    · have hne : (exp == 0) = false := beq_false_of_ne' h0
      have hdiv : exp / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hexp; omega
      rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hsq : ((base * base) % m) ^ (exp / 2) % m = base ^ (2 * (exp / 2)) % m := by
        rw [← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      rcases Nat.mod_two_eq_zero_or_one exp with heven | hodd
      · have hmod : (exp % 2 == 1) = false := by rw [heven]; rfl
        rw [hmod]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod, hsq, show 2 * (exp / 2) = exp by omega, ← Nat.mul_mod]
      · have hmod : (exp % 2 == 1) = true := by rw [hodd]; rfl
        rw [hmod]; simp only [↓reduceIte]
        rw [ih _ _ _ _ hdiv, Nat.mul_mod ((acc * base) % m), Nat.mod_mod, hsq, ← Nat.mul_mod,
            Nat.mul_assoc acc, ← Nat.pow_succ', show (2 * (exp / 2)).succ = exp by omega]

theorem fpPow_mod_eq_pow_mod (a e : Nat) (he : e < 2 ^ 256) :
    fpPow (a % p25519) e = a ^ e % p25519 := by
  unfold fpPow modPow
  rw [Nat.mod_mod, modPowLoop_eq 256 (a % p25519) e p25519 1 he, Nat.one_mul, ← Nat.pow_mod a e p25519]

/-- In `A ∗ (O ∗ S)`, the bytes owned by `O` and by `S` are different. -/
theorem ne_of_sat2 {A O S R C : SepProp} {φ : Prop} {m0 : Memory} {W1 W2 : BitVec 64 → Prop}
    (hs : m0 ⊨ ((⌜φ⌝ ∗ (A ∗ (O ∗ S))) ∗ C) ∗ R) (hO : OwnsRW O W1) (hS : OwnsRW S W2)
    {x y : BitVec 64} (hx : W1 x) (hy : W2 y) : x ≠ y := by
  obtain ⟨_, ⟨_, _, _, rfl, ⟨_, _, _, rfl, ⟨_, _, _, rfl, _, ⟨_, _, _, rfl, _, ⟨h1, h2, hd, rfl, o, s⟩⟩⟩, _⟩,
    _⟩, _⟩ := hs
  intro e; subst e
  obtain ⟨b1, e1⟩ := hO h1 o x hx
  obtain ⟨b2, e2⟩ := hS h2 s x hy
  rcases hd.1 x with e | e | ⟨b, e3, _⟩
  · rw [e] at e1; cases e1
  · rw [e] at e2; cases e2
  · rw [e3] at e1; cases e1

theorem fnOk_fe51_pow2k_dev :
    fnOk "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k"
      (fun _ => fe51Pow2kSpec) := by
  refine ⟨2, 0, rfl, fun mpl _ => ?_⟩
  rintro ⟨out, a, k, out_bs, a_bs⟩ R s0 hpc hrun hpre hal hCL
  have hfa : x25519CliMultiLib.fnAddr mpl
      "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k" =
      mpl.base 2 + BitVec.ofNat 64 0 := rfl
  rw [hfa] at hpc
  change s0.mem ⊨ ((⌜s0.readReg64 Reg.x8 = out ∧ s0.readReg64 Reg.x0 = a ∧ s0.readReg32 Reg.x1 = k ∧
      out_bs.length = 40 ∧ fe51LimbsBounded a_bs (2 ^ 54) ∧ 0 < k.toNat ∧ k.toNat < 256⌝ ∗
      (a ↦ₛ a_bs ∗ (out ↦ₛ out_bs ∗ memRegion (s0.sp - BitVec.ofNat 64 96) 96))) ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝) ∗ R at hpre
  have hφ := pure_of_sat (P := a ↦ₛ a_bs ∗ _) (by rw [sepConj_assoc] at hpre; exact hpre)
  obtain ⟨hx8, hx0, hx1, hlo, hba, hk1, hk2⟩ := hφ
  set W : BitVec 64 → Prop := fun x => InRegion (s0.sp - BitVec.ofNat 64 96) 96 x ∨ InRegion out 40 x
    with hWdef
  have hOwnO : OwnsRW (out ↦ₛ out_bs) (InRegion out 40) := by
    have := ownsRW_bytes out_bs out; rwa [hlo] at this
  have hOwnS := ownsRW_region (s0.sp - BitVec.ofNat 64 96) 96
  have hOwnQ : OwnsRW (out ↦ₛ out_bs ∗ memRegion (s0.sp - BitVec.ofNat 64 96) 96) W :=
    ownsRW_or (ownsRW_sep_right hOwnS) (ownsRW_sep_left hOwnO)
  have hOwnA := ownsRW_sep_right (P := a ↦ₛ a_bs) hOwnQ
  have hW := wowned_of hpre (ownsRW_sep_left (ownsRW_sep_right hOwnA))
  have bA := bytes_of_sat hpre (inCells_rw a_bs a) (Or.inl rfl) hOwnQ
  have la : a_bs.length = 40 := hba.1
  have hsp : s0.sp.toNat % 16 = 0 := (spAligned_iff s0).1 hal
  have hsp' : (s0.sp + 0xffffffffffffffa0#64).toNat % 16 = 0 := by
    rw [show s0.sp + 0xffffffffffffffa0#64 = s0.sp - BitVec.ofNat 64 96 by bv_omega]
    exact sp_sub_aligned hsp 96 rfl (by decide)
  have hstk : ∀ x : BitVec 64, (x - (s0.sp - 96#64)).toNat + 8 ≤ 96 → AllB W x 8 := by
    intro x hx j hj; left; unfold InRegion
    rw [show x + BitVec.ofNat 64 j - (s0.sp - BitVec.ofNat 64 96) =
      (x - (s0.sp - 96#64)) + BitVec.ofNat 64 j by bv_omega, BitVec.toNat_add, BitVec.toNat_ofNat]
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
  have hfar : ∀ c c' : BitVec 64, c.toNat + 8 ≤ 40 → (c' + 96#64).toNat + 8 ≤ 96 →
      Far (out + c) (s0.sp + c') := by
    intro c c' hc hc'
    refine far_of_ne fun j l hj hl => ne_of_sat2 hpre hOwnO hOwnS ?_ ?_
    · unfold InRegion
      rw [show out + c + BitVec.ofNat 64 j - out = c + BitVec.ofNat 64 j by bv_omega,
        BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · unfold InRegion
      rw [show s0.sp + c' + BitVec.ofNat 64 l - (s0.sp - BitVec.ofNat 64 96) =
        (c' + 96#64) + BitVec.ofNat 64 l by bv_omega, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
  have hfar0 : ∀ c' : BitVec 64, (c' + 96#64).toNat + 8 ≤ 96 → Far out (s0.sp + c') := by
    intro c' hc'
    have := hfar 0#64 c' (by decide) hc'
    rwa [BitVec.add_zero] at this
  have hrA : ∀ m c, MemOK s0.mem W m → c.toNat + 8 ≤ 40 → m.canRead (a + c) 8 = true := by
    intro m c hok hc
    have := canRead_buf bA hok c.toNat (by omega)
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  have hrA2 : ∀ m c, MemOK s0.mem W m → c.toNat + 16 ≤ 40 → m.canRead (a + c + 8#64) 8 = true := by
    intro m c hok hc
    have := canRead_buf bA hok (c.toNat + 8) (by omega)
    rwa [show a + BitVec.ofNat 64 (c.toNat + 8) = a + c + 8#64 by bv_omega] at this
  have rd : ∀ off, off + 8 ≤ 40 → ∀ m, MemOK s0.mem W m →
      m.read64 (a + BitVec.ofNat 64 off) = ByteSlice.readLE a_bs off 8 :=
    fun off ho m hok => read64_buf bA hok off (by omega)
  have ha : s0.regs.regs 0#5 = a := by simpa [State.readReg64, RegFile.read] using hx0
  have ho : s0.regs.regs 8#5 = out := by simpa [State.readReg64, RegFile.read] using hx8
  have hk : BitVec.truncate 32 (s0.regs.regs 1#5) = BitVec.ofNat 32 k.toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, ← hx1]
    simp [State.readReg32, State.readReg64, RegFile.read]
  show Reach mpl 2 _ s0
  apply reach_start
  rw [hpc, regL_init s0.regs.regs]
  refine p2k_run hCL hrun hW hsp hsp' hstk hout hout2 hfar hfar0 hrA hrA2
    (fun m hok => by simpa using rd 0 (by omega) m hok)
    (fun m hok => rd 8 (by omega) m hok)
    (fun m hok => rd 16 (by omega) m hok)
    (fun m hok => rd 24 (by omega) m hok)
    (fun m hok => rd 32 (by omega) m hok)
    hba.2 ha ho hk hk1 hk2 ?_
  intro L m ps l0 l1 l2 l3 l4 hcal hok e0 e1 e2 e3 e4 b0 b1 b2 b3 b4 hval
  refine outcome_of' hrun hcal (frame hpre hok (ownsRW_sep_left (ownsRW_sep_right hOwnA))
    (rf_mono (rf_sep (rf_sep (rf_pure' (fun _ => trivial))
      (rf_sep (rf_rw_same m a a_bs fun i hi => ?_)
        (rf_sep (rf_bytes m out_bs out) (rf_region _ _ _)))) (rf_pure' (fun _ => trivial))) ?_))
  · rw [(hok _).2.2.2 (bA i hi).2.2.2]; exact (bA i hi).1
  · rw [sepConj_pure_true, sepConj_comm, sepConj_pure_true, hlo]
    refine sep_mono_r ?_
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
        show out + BitVec.ofNat 64 32 = out + 32#64 from rfl, e4, hval,
        fpPow_mod_eq_pow_mod _ _ (Nat.pow_lt_pow_right (by norm_num) hk2)]

end X25519Dalek.Field
end

theorem solution :
    X25519Dalek.fnOk
      "<curve25519_dalek::backend::serial::u64::field::FieldElement51>::pow2k"
      (fun _ => X25519Dalek.fe51Pow2kSpec) :=
  X25519Dalek.Field.fnOk_fe51_pow2k_dev
