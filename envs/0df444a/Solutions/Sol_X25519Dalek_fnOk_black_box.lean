-- Prove2me | solution 1 for X25519Dalek.fnOk_black_box
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T09:34:53.062086+00:00
-- url     : https://prove2.me/submissions/7c2a7a41-a571-4916-a20a-3c38191ef06d

import Mathlib.Tactic.IntervalCases
import Definitions.Def_X25519Dalek_Spec

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

/-! ## 64-bit reads over 64-bit writes -/

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

theorem ownsRW_region (b : BitVec 64) (n : Nat) : OwnsRW (memRegion b n) (InRegion b n) := by
  rintro _ ⟨mm, rfl⟩ a ha
  exact ⟨mm.read8 a, by simp [regionHeap, ha]⟩

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

/-- `STRB Wt, [B, #off]`. -/
theorem ex_strb {t : BitVec 5} {B : Reg} {bv off : BitVec 64} (ht : t ≠ 31#5)
    (hB : (mkS s pc r sp m ps).readReg64 B = bv) (hal : checkRegSPAligned (mkS s pc r sp m ps) B = true)
    (hw : m.canWrite (bv + off) 1 = true) :
    execInstWithSvc svc (.str .B8 (.gpr t) (.Offset B off)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) r sp (m.write8 (bv + off) ((r t).truncate 8)) ps := by
  show execStr .B8 (.gpr t) (.Offset B off) (mkS s pc r sp m ps) = _
  simp only [execStr, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, hB, mkS_mem, MemWidth.bytes, hw,
    rd_gpr' _ _ _ _ _ _ _ ht, Memory.writeSized, mkS_setMem, mkS_advancePC]

/-- `LDRB Wd, [B, #off]`. -/
theorem ex_ldrb {d : BitVec 5} {B : Reg} {bv off : BitVec 64} (hd : d ≠ 31#5)
    (hB : (mkS s pc r sp m ps).readReg64 B = bv) (hal : checkRegSPAligned (mkS s pc r sp m ps) B = true)
    (hrd : m.canRead (bv + off) 1 = true) :
    execInstWithSvc svc (.ldr .W32 .B8 false (.gpr d) (.Offset B off)) (mkS s pc r sp m ps) =
      mkS s (pc + 4#64) (Function.update r d
        ((((m.read8 (bv + off)).zeroExtend 64).truncate 32).zeroExtend 64)) sp m ps := by
  show execLdr .W32 .B8 false (.gpr d) (.Offset B off) (mkS s pc r sp m ps) = _
  simp only [execLdr, checkAddrSPAligned, AddrMode.baseReg, hal, Bool.not_true,
    Bool.false_eq_true, if_false, evalAddrMode, hB, mkS_mem, MemWidth.bytes, hrd,
    Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC]

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
/-! # `subtle::black_box::<u8>` (block 0, 5 instructions) -/

namespace X25519Dalek.Field

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

theorem blk00 : x25519CliBlocks.getD 0 { code := [] } = x25519CliBlk00 := rfl

section fetch
variable {mpl : MultiPlacement} {m : Memory} (hCL : (prog mpl 0).CodeLoaded m)
include hCL

theorem f00_0 : rawFetch m (mpl.base 0 + BitVec.ofNat 64 0) =
    some (.addSubImm .W64 .SUB .sp .sp 0x010#12 false) :=
  fetch_plain blk00 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f00_4 : rawFetch m (mpl.base 0 + BitVec.ofNat 64 4) =
    some (.str .B8 (.gpr 0#5) (.Offset .sp 12#64)) :=
  fetch_plain blk00 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f00_8 : rawFetch m (mpl.base 0 + BitVec.ofNat 64 8) =
    some (.ldr .W32 .B8 false (.gpr 0#5) (.Offset .sp 12#64)) :=
  fetch_plain blk00 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f00_12 : rawFetch m (mpl.base 0 + BitVec.ofNat 64 12) =
    some (.addSubImm .W64 .ADD .sp .sp 0x010#12 false) :=
  fetch_plain blk00 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f00_16 : rawFetch m (mpl.base 0 + BitVec.ofNat 64 16) = some (.ret (.gpr 30#5)) :=
  fetch_plain blk00 (by decide) hCL (by decide) (by decide) rfl rfl

end fetch

theorem fnOk_black_box_dev : fnOk "subtle::black_box::<u8>" (fun _ => blackBoxU8Spec) := by
  refine ⟨0, 0, rfl, fun mpl _ => ?_⟩
  intro v R s0 hpc hrun hpre hal hCL
  have hfa : x25519CliMultiLib.fnAddr mpl "subtle::black_box::<u8>" =
      mpl.base 0 + BitVec.ofNat 64 0 := rfl
  rw [hfa] at hpc
  change s0.mem ⊨ ((⌜BitVec.truncate 8 (s0.readReg32 Reg.x0) = v⌝ ∗
      memRegion (s0.sp - BitVec.ofNat 64 16) 16) ∗ ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝) ∗ R
    at hpre
  have hφ : BitVec.truncate 8 (s0.readReg32 Reg.x0) = v := pure_of_sat (P := memRegion _ _)
    (by rw [sepConj_assoc] at hpre; exact hpre)
  set W : BitVec 64 → Prop := InRegion (s0.sp - BitVec.ofNat 64 16) 16 with hWdef
  have hOwn : OwnsRW ((⌜BitVec.truncate 8 (s0.readReg32 Reg.x0) = v⌝ ∗
      memRegion (s0.sp - BitVec.ofNat 64 16) 16) ∗ ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝) W :=
    ownsRW_sep_left (ownsRW_sep_right (ownsRW_region _ _))
  have hW := wowned_of hpre hOwn
  have hsp : s0.sp.toNat % 16 = 0 := (spAligned_iff s0).1 hal
  have hsp16 : (s0.sp - BitVec.ofNat 64 16).toNat % 16 = 0 := sp_sub_aligned hsp 16 rfl (by decide)
  have hok0 := memOK_refl s0.mem W
  have hWa : AllB W (s0.sp - BitVec.ofNat 64 16 + 12#64) 1 := by
    intro j hj
    show ((s0.sp - BitVec.ofNat 64 16 + 12#64 + BitVec.ofNat 64 j) -
      (s0.sp - BitVec.ofNat 64 16)).toNat < 16
    have : j = 0 := by omega
    subst this
    simp only [BitVec.add_zero]
    rw [show s0.sp - BitVec.ofNat 64 16 + 12#64 - (s0.sp - BitVec.ofNat 64 16) = 12#64 by bv_omega]
    decide
  show Reach mpl 0 _ s0
  apply reach_start
  rw [hpc]
  refine reach_mk hrun hW hok0 (f00_0 hCL) ?_
  rw [ex_subsp, pc_add4, show (0x010#12 : BitVec 12).zeroExtend 64 = BitVec.ofNat 64 16 from rfl]
  refine reach_mk hrun hW hok0 (f00_4 hCL) ?_
  rw [ex_strb (by decide) (rd_sp ..) (checkSP _ _ _ _ _ _ hsp16) (canWrite_of hW hok0 hWa), pc_add4]
  have hok1 := memOK_write8 hW hok0 (by simpa using hWa 0 (by omega)) (BitVec.truncate 8 (s0.regs.regs 0#5))
  refine reach_mk hrun hW hok1 (f00_8 hCL) ?_
  rw [ex_ldrb (by decide) (rd_sp ..) (checkSP _ _ _ _ _ _ hsp16) (canRead_of_W hW hok1 hWa), pc_add4]
  refine reach_mk hrun hW hok1 (f00_12 hCL) ?_
  rw [ex_addsp, pc_add4, show (0x010#12 : BitVec 12).zeroExtend 64 = BitVec.ofNat 64 16 from rfl,
    BitVec.sub_add_cancel]
  refine reach_mk hrun hW hok1 (f00_16 hCL) ?_
  rw [ex_ret, Function.update_of_ne (by decide)]
  refine reach_done (outcome_of hrun (fun k hk => ?_) ?_)
  · exact Function.update_of_ne (fun e => by subst e; simp at hk) _ _
  · refine frame hpre hok1 hOwn (rf_mono (rf_sep (rf_sep (rf_pure' (ψ := ?ψ) ?hψ)
      (rf_region _ _ _)) (rf_pure' (fun _ => trivial))) ?hent)
    case hent =>
      rw [sepConj_pure_true, sepConj_comm]
      intro h hh
      simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, blackBoxU8Spec, stackFrame, mkS_sp]
      exact hh
    case hψ =>
      intro _
      rw [← hφ]
      simp only [State.readReg32, rd_gpr, Function.update_self, read8_write8, if_pos rfl]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp [State.readReg64, RegFile.read, hi]

end X25519Dalek.Field
end

theorem solution : X25519Dalek.fnOk "subtle::black_box::<u8>" (fun _ => X25519Dalek.blackBoxU8Spec) :=
  X25519Dalek.Field.fnOk_black_box_dev
