-- Prove2me | solution 1 for X25519Dalek.fnOk_scalar_as_radix_16
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T11:18:28.120827+00:00
-- url     : https://prove2.me/submissions/f5fde2de-acc1-40c9-a624-9ba1e19db795

import Mathlib.Tactic.IntervalCases
import Definitions.Def_X25519Dalek_Spec

section
/-! # Instruction fetch for the hook-free x25519-dalek blocks, abstract states, Reach

Fetch lemmas follow the zlib CRC-32 proofs (`ZlibCrc32.Small.Machine`), generalised to a block of
the multi-block library `x25519CliMultiLib`. -/

namespace X25519Dalek.EF

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

end X25519Dalek.EF
end

section
/-! # Abstract states, reachability and one lemma per instruction shape -/

namespace X25519Dalek.EF

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

end X25519Dalek.EF
end

section
/-! # Memory: reads over writes, and the invariant that only owned writable bytes change -/

namespace X25519Dalek.EF

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

end X25519Dalek.EF
end

section
/-! # Heaps: refreshing the read-write cells after stores, and the frame rule -/

namespace X25519Dalek.EF

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

end X25519Dalek.EF
end

section
/-! # The frame rule for straight-line stores, and points-to facts -/

namespace X25519Dalek.EF

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

end X25519Dalek.EF
end

section
/-! # Execution of each instruction shape on an abstract state -/

namespace X25519Dalek.EF

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

end X25519Dalek.EF
end

section
/-! # Running a block: one step at a time from an abstract state; the outcome at `RET` -/

namespace X25519Dalek.EF

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

theorem checkGpr (s : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64)
    (m : Memory) (ps : PState) (k : BitVec 5) :
    checkRegSPAligned (mkS s pc r sp m ps) (.gpr k) = true := rfl

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

end X25519Dalek.EF
end

section
/-! # Straight-line execution in SSA form

Each lemma executes one instruction from an abstract state `mkS s (pcb + n) r sp m ps` and hands
the continuation a fresh name for the value written, with its defining equation. The register
file is kept as a literal list (`regL`), so that reads and writes normalise by `simp`. -/

namespace X25519Dalek.EF

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

end ssa

/-! ## Facts used by the normalisation -/

end X25519Dalek.EF
end

section
/-! # More instruction shapes: pre/post-indexed stack access, 32-bit `SUBS #1`, `B.NE` -/

namespace X25519Dalek.EF

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

section ssa
variable {mpl : MultiPlacement} {i : Nat} {P : State → Prop} {s : State} {pcb : BitVec 64}
  {n : Nat} {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {m m0 : Memory} {ps : PState}
  {W : BitVec 64 → Prop}

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

end X25519Dalek.EF

namespace X25519Dalek.EF

open Arm64 Arm64.Obj

end X25519Dalek.EF
end

section
/-! # Step lemmas for `Scalar::as_radix_16` (block 3): byte loads, nibble operations, and byte
stores into an output buffer tracked as a list -/

namespace X25519Dalek.EF

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-- The bytes at `o + j`, `j < L.length`, read `L`. -/
def OutL (m : Memory) (o : BitVec 64) (L : List (BitVec 8)) : Prop :=
  ∀ j, j < L.length → m.read8 (o + BitVec.ofNat 64 j) = L.getD j 0#8

theorem ofNat_add_inj {o : BitVec 64} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : o + BitVec.ofNat 64 i = o + BitVec.ofNat 64 j) : i = j := by
  have h2 : BitVec.ofNat 64 i = BitVec.ofNat 64 j := by
    have := congrArg (· - o) h; simpa using this
  have := congrArg BitVec.toNat h2
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact this

theorem outL_write {m : Memory} {o : BitVec 64} {L : List (BitVec 8)} (h : OutL m o L) {j : Nat}
    (hj : j < L.length) (hL : L.length < 2 ^ 64) (v : BitVec 8) :
    OutL (m.write8 (o + BitVec.ofNat 64 j) v) o (L.set j v) := by
  intro k hk
  rw [List.length_set] at hk
  rw [read8_write8]
  by_cases hkj : k = j
  · subst hkj; rw [if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]; rfl
  · rw [if_neg (fun e => hkj (ofNat_add_inj (by omega) (by omega) e)), h k hk,
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hkj)]

theorem ze8_32 (x : BitVec 8) :
    (((x.zeroExtend 64).truncate 32).zeroExtend 64 : BitVec 64) = x.zeroExtend 64 := by
  revert x; decide

theorem wr_gpr_ite (s : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (sp : BitVec 64)
    (m : Memory) (ps : PState) (i : BitVec 5) (v : BitVec 64) :
    (mkS s pc r sp m ps).writeReg64 (.gpr i) v =
      if i = 31#5 then mkS s pc r sp m ps else mkS s pc (Function.update r i v) sp m ps := by
  split
  · subst_vars; rfl
  · exact wr_gpr s pc r sp m ps i v ‹_›

section steps
variable {mpl : MultiPlacement} {i : Nat} {P : State → Prop} {s : State} {pcb : BitVec 64}
  {n : Nat} {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {m m0 : Memory} {ps : PState}
  {W : BitVec 64 → Prop}

/-- `LDRB Wd, [Xb, #k]`. -/
theorem r_ldrb {d b : BitVec 5} {k : Nat} {A : BitVec 64} (hd : d ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.ldr .W32 .B8 false (.gpr d) (.Offset (.gpr b) (BitVec.ofNat 64 k))))
    (hA : r b = A) (hrd : m.canRead (A + BitVec.ofNat 64 k) 1 = true)
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r d ((m.read8 (A + BitVec.ofNat 64 k)).zeroExtend 64)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  refine reach_mk hrun hW hok hf ?_
  rw [ex_ldrb hd (by rw [rd_gpr' _ _ _ _ _ _ _ hb, hA]) (checkGpr ..) hrd, pc_add4, ze8_32]
  exact h

/-- `AND Wd, Wn, #0xf` on a byte. -/
theorem r_and15 {d a : BitVec 5} {x : BitVec 8} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.logicalImm .W32 .AND (.gpr d) (.gpr a) 0x0000000f0000000f#64))
    (hx : r a = x.zeroExtend 64)
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r d ((x &&& 15#8).zeroExtend 64)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  refine reach_mk hrun hW hok hf ?_
  have e : execInstWithSvc (evalSvc Syscall.standard)
      (.logicalImm .W32 .AND (.gpr d) (.gpr a) 0x0000000f0000000f#64)
      (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) =
      mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d ((x &&& 15#8).zeroExtend 64)) sp m ps := by
    show ((mkS s _ r sp m ps).writeReg .W32 (.gpr d) _).advancePC = _
    simp only [State.writeReg, State.readReg, State.readReg32, rd_gpr' _ _ _ _ _ _ _ ha, hx,
      evalLogical, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC, pc_add4]
    congr 2
    clear h hx; revert x; decide
  rw [e]; exact h

/-- `LSR Wd, Wn, #4` (`UBFM Wd, Wn, #4, #31`) on a byte. -/
theorem r_lsr4 {d a : BitVec 5} {x : BitVec 8} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.bitfield .W32 .UBFM (.gpr d) (.gpr a) 4 31))
    (hx : r a = x.zeroExtend 64)
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r d ((x >>> 4).zeroExtend 64)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  refine reach_mk hrun hW hok hf ?_
  have e : execInstWithSvc (evalSvc Syscall.standard) (.bitfield .W32 .UBFM (.gpr d) (.gpr a) 4 31)
      (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) =
      mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r d ((x >>> 4).zeroExtend 64)) sp m ps := by
    show ((mkS s _ r sp m ps).writeReg .W32 (.gpr d) _).advancePC = _
    simp only [State.writeReg, State.readReg, State.readReg32, rd_gpr' _ _ _ _ _ _ _ ha,
      rd_gpr' _ _ _ _ _ _ _ hd, hx, wr_gpr _ _ _ _ _ _ _ _ hd, mkS_advancePC, pc_add4]
    congr 2
    simp only [evalBitfield]
    clear h hx; revert x; decide
  rw [e]; exact h

/-- `STRB Wt, [Xb, #j]` into the tracked buffer. -/
theorem r_strbO {t b : BitVec 5} {j : Nat} {o : BitVec 64} {x : BitVec 8} {L : List (BitVec 8)}
    (ht : t ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.str .B8 (.gpr t) (.Offset (.gpr b) (BitVec.ofNat 64 j))))
    (ho : r b = o) (hx : r t = x.zeroExtend 64) (hL : OutL m o L) (hj : j < L.length)
    (hLl : L.length < 2 ^ 64) (hWj : W (o + BitVec.ofNat 64 j))
    (h : ∀ m', MemOK m0 W m' → OutL m' o (L.set j x) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r sp m' ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  have hw : m.canWrite (o + BitVec.ofNat 64 j) 1 = true :=
    canWrite_of hW hok (fun k hk => by
      have : k = 0 := by omega
      subst this; simpa using hWj)
  refine reach_mk hrun hW hok hf ?_
  rw [ex_strb ht (by rw [rd_gpr' _ _ _ _ _ _ _ hb, ho]) (checkGpr ..) hw, pc_add4]
  have hv : (r t).truncate 8 = x := by
    rw [hx]; apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
  rw [hv]
  exact h _ (memOK_write8 hW hok hWj x) (outL_write hL hj hLl x)

end steps

end X25519Dalek.EF
end

section
/-! # Fetch lemmas for block 3 (`Scalar::as_radix_16`, 173 words), generated from the decoder -/

namespace X25519Dalek.EF

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

theorem blk03 : x25519CliBlocks.getD 3 { code := [] } = x25519CliBlk03 := rfl

section fetch
variable {mpl : MultiPlacement} {m : Memory} (hCL : (prog mpl 3).CodeLoaded m)
include hCL

theorem f03_0 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 0) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000000#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_4 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 4) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000001#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_8 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 8) =
    some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x08#5) 0x003f#16 0) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_12 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 12) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000002#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_16 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 16) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x09#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_20 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 20) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_24 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 24) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0a#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_28 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 28) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_32 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 32) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000002#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_36 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 36) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0b#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_40 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 40) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_44 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 44) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000004#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_48 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 48) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000003#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_52 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 52) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000003#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_56 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 56) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_60 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 60) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000005#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_64 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 64) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_68 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 68) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000006#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_72 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 72) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000004#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_76 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 76) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000005#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_80 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 80) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000007#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_84 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 84) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_88 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 88) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_92 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 92) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000008#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_96 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 96) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_100 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 100) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000009#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_104 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 104) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_108 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 108) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000007#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_112 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 112) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000000a#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_116 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 116) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000006#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_120 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 120) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000000b#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_124 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 124) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_128 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 128) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_132 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 132) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000000c#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_136 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 136) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_140 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 140) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000000d#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_144 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 144) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_148 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 148) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000009#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_152 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 152) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000000e#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_156 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 156) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000008#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_160 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 160) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000000f#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_164 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 164) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_168 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 168) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_172 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 172) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000010#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_176 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 176) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_180 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 180) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000011#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_184 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 184) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_188 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 188) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x000000000000000b#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_192 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 192) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000012#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_196 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 196) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x000000000000000a#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_200 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 200) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000013#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_204 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 204) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_208 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 208) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_212 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 212) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000014#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_216 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 216) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_220 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 220) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000015#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_224 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 224) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_228 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 228) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x000000000000000d#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_232 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 232) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000016#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_236 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 236) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x000000000000000c#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_240 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 240) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000017#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_244 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 244) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_248 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 248) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_252 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 252) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000018#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_256 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 256) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_260 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 260) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000019#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_264 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 264) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_268 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 268) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x000000000000000f#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_272 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 272) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000001a#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_276 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 276) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x000000000000000e#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_280 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 280) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000001b#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_284 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 284) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_288 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 288) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_292 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 292) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000001c#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_296 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 296) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_300 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 300) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000001d#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_304 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 304) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_308 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 308) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000011#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_312 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 312) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000001e#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_316 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 316) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000010#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_320 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 320) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000001f#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_324 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 324) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_328 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 328) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_332 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 332) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000020#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_336 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 336) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_340 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 340) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000021#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_344 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 344) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_348 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 348) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000013#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_352 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 352) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000022#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_356 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 356) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000012#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_360 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 360) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000023#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_364 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 364) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_368 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 368) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_372 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 372) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000024#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_376 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 376) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_380 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 380) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000025#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_384 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 384) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_388 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 388) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000015#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_392 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 392) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000026#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_396 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 396) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000014#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_400 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 400) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000027#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_404 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 404) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_408 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 408) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_412 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 412) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000028#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_416 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 416) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_420 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 420) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000029#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_424 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 424) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_428 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 428) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000017#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_432 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 432) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000002a#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_436 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 436) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000016#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_440 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 440) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000002b#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_444 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 444) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_448 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 448) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_452 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 452) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000002c#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_456 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 456) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_460 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 460) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000002d#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_464 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 464) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_468 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 468) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000019#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_472 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 472) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000002e#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_476 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 476) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x0000000000000018#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_480 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 480) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000002f#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_484 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 484) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_488 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 488) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_492 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 492) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000030#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_496 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 496) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_500 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 500) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000031#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_504 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 504) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_508 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 508) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x000000000000001b#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_512 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 512) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000032#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_516 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 516) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x000000000000001a#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_520 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 520) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000033#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_524 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 524) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_528 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 528) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_532 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 532) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000034#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_536 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 536) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_540 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 540) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000035#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_544 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 544) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_548 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 548) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x000000000000001d#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_552 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 552) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000036#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_556 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 556) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x000000000000001c#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_560 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 560) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000037#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_564 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 564) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_568 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 568) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_572 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 572) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000038#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_576 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 576) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_580 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 580) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000039#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_584 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 584) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_588 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 588) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x000000000000001f#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_592 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 592) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000003a#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_596 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 596) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x01#5) 0x000000000000001e#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_600 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 600) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000003b#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_604 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 604) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_608 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 608) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_612 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 612) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000003c#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_616 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 616) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_620 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 620) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000003d#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_624 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 624) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0c#5) 0x0000000f0000000f#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_628 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 628) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.UBFM) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x09#5) 4 31) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_632 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 632) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_636 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 636) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000003e#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_640 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 640) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x000000000000003f#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_644 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 644) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.gpr 0x00#5) 0x0000000000000001#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_648 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 648) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x09#5) 0x008#12 false) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_652 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 652) =
    some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_656 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 656) =
    some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) 0x001#12 false) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_660 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 660) =
    some (Arm64.Instr.bitfield (Arm64.RegWidth.W32) (Arm64.BitfieldOp.SBFM) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0a#5) 0 7) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_664 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 664) =
    some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 0x000000f0000000f0#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_668 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 668) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.ShiftType.LSL) 0) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_672 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 672) =
    some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.ASR) 4) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_676 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 676) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x00#5) 0xffffffffffffffff#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_680 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 680) =
    some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.gpr 0x00#5) 0x0000000000000001#64)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_684 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 684) =
    some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0xffffffffffffffdc#64) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl
theorem f03_688 : rawFetch m (mpl.base 3 + BitVec.ofNat 64 688) =
    some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) :=
  fetch_plain blk03 (by decide) hCL (by decide) (by decide) rfl rfl

end fetch

end X25519Dalek.EF
end

section
/-! # Step lemmas for the recentering loop of `Scalar::as_radix_16` (offsets 648–684) -/

namespace X25519Dalek.EF

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

section steps
variable {mpl : MultiPlacement} {i : Nat} {P : State → Prop} {s : State} {pcb : BitVec 64}
  {n : Nat} {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {m m0 : Memory} {ps : PState}
  {W : BitVec 64 → Prop}

theorem v_add8 : ∀ d, d ≤ 16 →
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64
      (AddWithCarry32 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 d))))
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (8#12 : BitVec 12))) false).1)) =
    BitVec.ofNat 64 (d + 8) := by decide

/-- `ADD W10, W9, #8`. -/
theorem r_add8 {d : Nat} (hd : d ≤ 16)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.addSubImm .W32 .ADD (.gpr 10#5) (.gpr 9#5) 0x008#12 false))
    (h9 : r 9#5 = BitVec.ofNat 64 d)
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r 10#5 (BitVec.ofNat 64 (d + 8))) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  refine reach_mk hrun hW hok hf ?_
  simp (config := {decide := true}) only [execInstWithSvc, execAddSubImm, State.readReg,
    State.readReg32, rd_gpr, evalAddSub, State.writeReg, wr_gpr_ite, mkS_advancePC, pc_add4, h9,
    Bool.false_eq_true, if_false, ↓reduceIte, v_add8 d hd]
  exact h

/-- `SUBS X8, X8, #1`. -/
theorem r_subsx1
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.addSubImm .W64 .SUBS (.gpr 8#5) (.gpr 8#5) 0x001#12 false))
    (h : ∀ ps', ps'.z = decide (r 8#5 - 1#64 = 0#64) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
        (Function.update r 8#5 (r 8#5 - 1#64)) sp m ps')) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  refine reach_mk hrun hW hok hf ?_
  simp (config := {decide := true}) only [execInstWithSvc, execAddSubImm, State.readReg,
    rd_gpr, evalAddSub, State.writeReg, wr_gpr_ite, mkS_advancePC, pc_add4, mkS_setPState,
    Bool.false_eq_true, if_false, if_true, ↓reduceIte]
  have e1 : (AddWithCarry64 (r 8#5) (~~~BitVec.zeroExtend 64 (1#12 : BitVec 12)) true).1 = r 8#5 - 1#64 := by
    rw [show BitVec.zeroExtend 64 (1#12 : BitVec 12) = 1#64 from rfl, awc_sub]
  rw [e1]
  refine h _ ?_
  rw [show (AddWithCarry64 (r 8#5) (~~~BitVec.zeroExtend 64 (1#12 : BitVec 12)) true).2.z =
    ((AddWithCarry64 (r 8#5) (~~~BitVec.zeroExtend 64 (1#12 : BitVec 12)) true).1 == 0#64) from rfl, e1]
  by_cases hz : r 8#5 - 1#64 = 0#64 <;> simp [hz]

/-- `SXTB W11, W10` on a value below 128. -/
theorem r_sxtb {e : Nat} (he : e < 128)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) = some (.bitfield .W32 .SBFM (.gpr 11#5) (.gpr 10#5) 0 7))
    (h10 : r 10#5 = BitVec.ofNat 64 e)
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r 11#5 (BitVec.ofNat 64 e)) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  refine reach_mk hrun hW hok hf ?_
  simp (config := {decide := true}) only [execInstWithSvc, execBitfield, evalBitfield, State.readReg,
    State.readReg32, rd_gpr, State.writeReg, wr_gpr_ite, mkS_advancePC, pc_add4, h10,
    Bool.false_eq_true, if_false, ↓reduceIte, if_true, Nat.reduceMod]
  convert h using 4
  clear h h10 hf
  revert he; revert e; decide

/-- `AND W10, W10, #0xf0` on a value below 128. -/
theorem r_andf0 {e : Nat} (he : e < 128)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.logicalImm .W32 .AND (.gpr 10#5) (.gpr 10#5) 0x000000f0000000f0#64))
    (h10 : r 10#5 = BitVec.ofNat 64 e)
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r 10#5 (BitVec.ofNat 64 (e / 16 * 16))) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  refine reach_mk hrun hW hok hf ?_
  simp (config := {decide := true}) only [execInstWithSvc, execLogicalImm, evalLogical,
    State.readReg, State.readReg32, rd_gpr, State.writeReg, wr_gpr_ite, mkS_advancePC, pc_add4,
    h10, Bool.false_eq_true, if_false, ↓reduceIte, if_true]
  convert h using 4
  clear h h10 hf
  revert he; revert e; decide

/-- `SUB W10, W9, W10`. -/
theorem r_subw {d : Nat} (hd : d ≤ 16)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.addSubShift .W32 .SUB (.gpr 10#5) (.gpr 9#5) (.gpr 10#5) .LSL 0))
    (h9 : r 9#5 = BitVec.ofNat 64 d) (h10 : r 10#5 = BitVec.ofNat 64 ((d + 8) / 16 * 16))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r 10#5 ((BitVec.ofInt 32 (Int.ofNat d - (Int.ofNat d + 8) / 16 * 16)).zeroExtend 64))
        sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  refine reach_mk hrun hW hok hf ?_
  simp (config := {decide := true}) only [execInstWithSvc, execAddSubShift, evalAddSub, shiftVal,
    State.readReg, State.readReg32, rd_gpr, State.writeReg, wr_gpr_ite, mkS_advancePC, pc_add4,
    h9, h10, ↓reduceIte, if_true, mkS_setPState]
  convert h using 4
  clear h h9 h10 hf
  revert hd; revert d; decide

/-- `ADD W9, W12, W11, ASR #4`. -/
theorem r_addasr {d b : Nat} (hd : d ≤ 16) (hb : b < 16)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.addSubShift .W32 .ADD (.gpr 9#5) (.gpr 12#5) (.gpr 11#5) .ASR 4))
    (h12 : r 12#5 = BitVec.ofNat 64 b) (h11 : r 11#5 = BitVec.ofNat 64 (d + 8))
    (h : Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
      (Function.update r 9#5 (BitVec.ofNat 64 (b + (d + 8) / 16))) sp m ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  refine reach_mk hrun hW hok hf ?_
  simp (config := {decide := true}) only [execInstWithSvc, execAddSubShift, evalAddSub, shiftVal,
    State.readReg, State.readReg32, rd_gpr, State.writeReg, wr_gpr_ite, mkS_advancePC, pc_add4,
    h12, h11, ↓reduceIte, if_true, if_false, Bool.false_eq_true, mkS_setPState]
  convert h using 4
  clear h h12 h11 hf
  revert hb; revert b; revert hd; revert d; decide

/-- `STURB Wt, [Xb, #-1]` into the tracked buffer. -/
theorem r_sturbO {t b : BitVec 5} {j : Nat} {o p : BitVec 64} {x : BitVec 8} {L : List (BitVec 8)}
    (ht : t ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.str .B8 (.gpr t) (.UnscaledOffset (.gpr b) 0xffffffffffffffff#64)))
    (hp : r b = p) (hpj : p + 0xffffffffffffffff#64 = o + BitVec.ofNat 64 j)
    (hx : (r t).truncate 8 = x) (hL : OutL m o L) (hj : j < L.length)
    (hLl : L.length < 2 ^ 64) (hWj : W (o + BitVec.ofNat 64 j))
    (h : ∀ m', MemOK m0 W m' → OutL m' o (L.set j x) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) r sp m' ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  have hw : m.canWrite (o + BitVec.ofNat 64 j) 1 = true :=
    canWrite_of hW hok (fun k hk => by
      have : k = 0 := by omega
      subst this; simpa using hWj)
  refine reach_mk hrun hW hok hf ?_
  simp (config := {decide := true}) only [execInstWithSvc, execStr, checkAddrSPAligned,
    checkRegSPAligned, AddrMode.baseReg, evalAddrMode, MemWidth.bytes, rd_gpr, if_neg hb, if_neg ht,
    hp, hpj, mkS_mem, hw, Bool.not_true, Bool.false_eq_true, if_false, Memory.writeSized,
    mkS_setMem, mkS_advancePC, pc_add4, hx]
  exact h _ (memOK_write8 hW hok hWj x) (outL_write hL hj hLl x)

/-- `STRB Wt, [Xb], #1` into the tracked buffer. -/
theorem r_strb_postO {t b : BitVec 5} {j : Nat} {o p : BitVec 64} {x : BitVec 8} {L : List (BitVec 8)}
    (ht : t ≠ 31#5) (hb : b ≠ 31#5) (htb : t ≠ b)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.str .B8 (.gpr t) (.PostIndex (.gpr b) 0x0000000000000001#64)))
    (hp : r b = p) (hpj : p = o + BitVec.ofNat 64 j)
    (hx : (r t).truncate 8 = x) (hL : OutL m o L) (hj : j < L.length)
    (hLl : L.length < 2 ^ 64) (hWj : W (o + BitVec.ofNat 64 j))
    (h : ∀ m', MemOK m0 W m' → OutL m' o (L.set j x) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4)) (Function.update r b (p + 1#64)) sp m' ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  subst hpj
  have hw : m.canWrite (o + BitVec.ofNat 64 j) 1 = true :=
    canWrite_of hW hok (fun k hk => by
      have : k = 0 := by omega
      subst this; simpa using hWj)
  refine reach_mk hrun hW hok hf ?_
  simp (config := {decide := true}) only [execInstWithSvc, execStr, checkAddrSPAligned,
    checkRegSPAligned, AddrMode.baseReg, evalAddrMode, MemWidth.bytes, rd_gpr, hp, mkS_mem,
    Bool.not_true, Bool.false_eq_true, if_false, ↓reduceIte, Memory.writeSized, mkS_setMem,
    mkS_advancePC, pc_add4, hx, if_neg ht, if_neg hb, wr_gpr_ite, hw]
  exact h _ (memOK_write8 hW hok hWj x) (outL_write hL hj hLl x)

/-- `STRB Wt, [Xb, #1]!` into the tracked buffer. -/
theorem r_strb_preO {t b : BitVec 5} {j : Nat} {o p : BitVec 64} {x : BitVec 8} {L : List (BitVec 8)}
    (ht : t ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    (hf : rawFetch m0 (pcb + BitVec.ofNat 64 n) =
      some (.str .B8 (.gpr t) (.PreIndex (.gpr b) 0x0000000000000001#64)))
    (hp : r b = p) (hpj : p + 1#64 = o + BitVec.ofNat 64 j)
    (hx : (r t).truncate 8 = x) (hL : OutL m o L) (hj : j < L.length)
    (hLl : L.length < 2 ^ 64) (hWj : W (o + BitVec.ofNat 64 j))
    (h : ∀ m', MemOK m0 W m' → OutL m' o (L.set j x) →
      Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 (n + 4))
        (Function.update r b (o + BitVec.ofNat 64 j)) sp m' ps)) :
    Reach mpl i P (mkS s (pcb + BitVec.ofNat 64 n) r sp m ps) := by
  have hw : m.canWrite (o + BitVec.ofNat 64 j) 1 = true :=
    canWrite_of hW hok (fun k hk => by
      have : k = 0 := by omega
      subst this; simpa using hWj)
  refine reach_mk hrun hW hok hf ?_
  simp (config := {decide := true}) only [execInstWithSvc, execStr, checkAddrSPAligned,
    checkRegSPAligned, AddrMode.baseReg, evalAddrMode, MemWidth.bytes, rd_gpr, hp, mkS_mem,
    Bool.not_true, Bool.false_eq_true, if_false, ↓reduceIte, Memory.writeSized, mkS_setMem,
    mkS_advancePC, pc_add4, hx, if_neg ht, if_neg hb, wr_gpr_ite, hpj, hw]
  exact h _ (memOK_write8 hW hok hWj x) (outL_write hL hj hLl x)

end steps

end X25519Dalek.EF
end

section
/-! # The digits of `Scalar::as_radix_16` as the loop computes them

`recenterNibbles`, `nibbleAt`, `nibblesFrom` and `scalarRadix16Digits_eq_recenterNibbles` are from
google-deepmind/code-verification @ 8c8d371f (Apache-2.0), `Shared51/ScalarRadix16.lean`. -/

namespace X25519Dalek.EF

open X25519Dalek

def recenterNibbles (d : Nat) : List (BitVec 8) → List (BitVec 8)
  | [] => [BitVec.ofNat 8 d]
  | b :: bs => BitVec.ofInt 8 (Int.ofNat d - (Int.ofNat d + 8) / 16 * 16) ::
      recenterNibbles (b.toNat + (d + 8) / 16) bs

def allNibbles : List (BitVec 8) → Prop
  | [] => True
  | x :: xs => x.toNat < 16 ∧ allNibbles xs

def nibbleAt (a_bs : List (BitVec 8)) (i : Nat) : BitVec 8 :=
  if i % 2 == 0 then a_bs.getD (i / 2) 0#8 &&& 15#8 else a_bs.getD (i / 2) 0#8 >>> 4

def nibblesFrom (a_bs : List (BitVec 8)) : Nat → List (BitVec 8)
  | 0 => []
  | k + 1 => nibbleAt a_bs (63 - k) :: nibblesFrom a_bs k

theorem nibbleAt_toNat_int_eq (a_bs : List (BitVec 8)) (i : Nat) :
    (if i % 2 == 0 then Int.ofNat ((a_bs.getD (i / 2) 0#8).toNat &&& 0x0f)
      else Int.ofNat ((a_bs.getD (i / 2) 0#8).toNat >>> 4)) = Int.ofNat (nibbleAt a_bs i).toNat := by
  unfold nibbleAt; split <;> simp [BitVec.toNat_and, BitVec.toNat_ushiftRight]

theorem scalarRadix16Digits_go_eq_recenterNibbles (a_bs : List (BitVec 8)) :
    ∀ (k : Nat) (_hk : k ≤ 63) (carry : Nat) (acc : List (BitVec 8)),
      scalarRadix16Digits.go a_bs (k + 1) (Int.ofNat carry) acc =
        acc.reverse ++ recenterNibbles ((nibbleAt a_bs (63 - k)).toNat + carry) (nibblesFrom a_bs k) := by
  intro k; induction k with
  | zero =>
    intro _ carry acc; rw [scalarRadix16Digits.go, nibbleAt_toNat_int_eq]
    change scalarRadix16Digits.go a_bs 0 0
      (BitVec.ofNat 8 ((nibbleAt a_bs 63).toNat + carry) :: acc) = _
    rw [scalarRadix16Digits.go]; simp [nibblesFrom, recenterNibbles]
  | succ m ih =>
    intro hk carry acc; rw [scalarRadix16Digits.go, nibbleAt_toNat_int_eq]
    have hm : 63 - (m + 1) < 63 := by omega
    let dNat := (nibbleAt a_bs (63 - (m + 1))).toNat + carry
    change (if 63 - (m + 1) < 63 then
        scalarRadix16Digits.go a_bs (m + 1) (Int.ofNat ((dNat + 8) / 16))
          (BitVec.ofInt 8 (Int.ofNat dNat - (Int.ofNat dNat + 8) / 16 * 16) :: acc)
      else scalarRadix16Digits.go a_bs (m + 1) 0 (BitVec.ofInt 8 (Int.ofNat dNat) :: acc)) = _
    simp only [hm, ↓reduceIte]; rw [ih (by omega) ((dNat + 8) / 16)]
    simp [nibblesFrom, recenterNibbles, dNat]

theorem scalarRadix16Digits_eq_recenterNibbles (a_bs : List (BitVec 8)) :
    scalarRadix16Digits a_bs = recenterNibbles (nibbleAt a_bs 0).toNat (nibblesFrom a_bs 63) := by
  unfold scalarRadix16Digits
  simpa using scalarRadix16Digits_go_eq_recenterNibbles a_bs 63 (by omega) 0 []

end X25519Dalek.EF
end

section
/-! # The recentering loop of `Scalar::as_radix_16`: one iteration, and all of them -/

namespace X25519Dalek.EF

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

theorem v_store1 : ∀ d, d ≤ 16 →
    ((BitVec.ofInt 32 (Int.ofNat d - (Int.ofNat d + 8) / 16 * 16)).zeroExtend 64 : BitVec 64).truncate 8 =
      BitVec.ofInt 8 (Int.ofNat d - (Int.ofNat d + 8) / 16 * 16) := by decide

theorem v_store2 (e : Nat) : (BitVec.ofNat 64 e).truncate 8 = BitVec.ofNat 8 e := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mod_mod_of_dvd]

theorem ze_byte (x : BitVec 8) : (x.zeroExtend 64 : BitVec 64) = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq; simp

/-- One iteration of the loop (offsets 648–684). -/
theorem iter {mpl : MultiPlacement} {P : State → Prop} {s : State} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {m m0 : Memory} {ps : PState} {W : BitVec 64 → Prop}
    (hCL : (prog mpl 3).CodeLoaded m0)
    (hrun : s.status = .Running) (hW : WOwned m0 W) (hok : MemOK m0 W m)
    {o : BitVec 64} {L : List (BitVec 8)} {q d c : Nat}
    (hL : OutL m o L) (hlen : L.length = 64) (hq1 : 1 ≤ q) (hq : q < 64) (hd : d ≤ 16)
    (hb : (L.getD q 0#8).toNat < 16) (hc1 : 1 ≤ c) (hc : c < 64)
    (hWo : ∀ k, k < 64 → W (o + BitVec.ofNat 64 k))
    (h0 : r 0#5 = o + BitVec.ofNat 64 q) (h8 : r 8#5 = BitVec.ofNat 64 c)
    (h9 : r 9#5 = BitVec.ofNat 64 d)
    (hrd : ∀ m', MemOK m0 W m' → m'.canRead (o + BitVec.ofNat 64 q + 0#64) 1 = true)
    (h : ∀ r' m' ps', MemOK m0 W m' →
      OutL m' o ((L.set (q - 1) (BitVec.ofInt 8 (Int.ofNat d - (Int.ofNat d + 8) / 16 * 16))).set q
        (BitVec.ofNat 8 ((L.getD q 0#8).toNat + (d + 8) / 16))) →
      r' 0#5 = o + BitVec.ofNat 64 (q + 1) → r' 8#5 = BitVec.ofNat 64 (c - 1) →
      r' 9#5 = BitVec.ofNat 64 ((L.getD q 0#8).toNat + (d + 8) / 16) →
      (∀ k : BitVec 5, 13 ≤ k.toNat → r' k = r k) →
      Reach mpl 3 P (mkS s (mpl.base 3 + BitVec.ofNat 64 (if c - 1 = 0 then 688 else 648)) r' sp m' ps')) :
    Reach mpl 3 P (mkS s (mpl.base 3 + BitVec.ofNat 64 648) r sp m ps) := by
  set b := (L.getD q 0#8).toNat with hbdef
  have hrq : m.read8 (o + BitVec.ofNat 64 q + 0#64) = BitVec.ofNat 8 b := by
    rw [BitVec.add_zero, hL q (by omega), hbdef]; simp
  refine r_add8 hd hrun hW hok (f03_648 hCL) h9 ?_
  refine r_ldrb (d := 12#5) (b := 0#5) (k := 0) (A := o + BitVec.ofNat 64 q) (by decide)
    (by decide) hrun hW hok (f03_652 hCL) (by rw [Function.update_of_ne (by decide), h0]) (hrd m hok) ?_
  rw [hrq, ze_byte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : b < 2 ^ 8)]
  refine r_subsx1 hrun hW hok (f03_656 hCL) (fun ps' hz => ?_)
  refine r_sxtb (e := d + 8) (by omega) hrun hW hok (f03_660 hCL)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]) ?_
  refine r_andf0 (e := d + 8) (by omega) hrun hW hok (f03_664 hCL)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self]) ?_
  refine r_subw hd hrun hW hok (f03_668 hCL)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), h9])
    (by rw [Function.update_self]) ?_
  refine r_addasr hd (by omega) hrun hW hok (f03_672 hCL)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self])
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]) ?_
  have hpj : o + BitVec.ofNat 64 q + 0xffffffffffffffff#64 = o + BitVec.ofNat 64 (q - 1) := by
    rw [BitVec.add_assoc]
    have key : BitVec.ofNat 64 q + 0xffffffffffffffff#64 = BitVec.ofNat 64 (q - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have e : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
      rw [e]
      omega
    rw [key]
  refine r_sturbO (t := 10#5) (b := 0#5) (j := q - 1) (p := o + BitVec.ofNat 64 q)
    (x := BitVec.ofInt 8 (Int.ofNat d - (Int.ofNat d + 8) / 16 * 16)) (by decide) (by decide)
    hrun hW hok (f03_676 hCL)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), h0])
    hpj (by rw [Function.update_of_ne (by decide), Function.update_self, v_store1 d hd])
    hL (by omega) (by omega) (hWo _ (by omega)) (fun m1 hok1 hL1 => ?_)
  refine r_strb_postO (t := 9#5) (b := 0#5) (j := q) (p := o + BitVec.ofNat 64 q)
    (x := BitVec.ofNat 8 (b + (d + 8) / 16)) (by decide) (by decide) (by decide) hrun hW hok1
    (f03_680 hCL)
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), h0]) rfl
    (by rw [Function.update_self, v_store2])
    hL1 (by rw [List.length_set]; omega) (by rw [List.length_set]; omega) (hWo _ hq)
    (fun m2 hok2 hL2 => ?_)
  have h8' : r 8#5 - 1#64 = BitVec.ofNat 64 (c - 1) := by
    rw [h8]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have e : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
    rw [e]; omega
  have hz' : ps'.z = decide (c - 1 = 0) := by
    rw [hz, Function.update_of_ne (by decide), Function.update_of_ne (by decide), h8']
    by_cases hc0 : c - 1 = 0
    · simp [hc0]
    · have : BitVec.ofNat 64 (c - 1) ≠ 0#64 := by
        intro e; have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; simp at this; omega
      simp [hc0, this]
  have h' := fun r' => h r' m2 ps' hok2 hL2
  have e1 : o + BitVec.ofNat 64 q + 1#64 = o + BitVec.ofNat 64 (q + 1) := by
    have e2 : BitVec.ofNat 64 q + 1#64 = BitVec.ofNat 64 (q + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have e : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
      rw [e]; omega
    rw [BitVec.add_assoc, e2]
  by_cases hc0 : c - 1 = 0
  · rw [if_pos hc0] at h'
    refine r_bne_not (by rw [hz']; simp [hc0]) hrun hW hok2 (f03_684 hCL) (h' _ ?_ ?_ ?_ ?_)
    · rw [Function.update_self]; exact e1
    · simp (config := {decide := true}) only [Function.update_apply, ↓reduceIte, if_true, if_false]
      exact h8'
    · simp (config := {decide := true}) only [Function.update_apply, ↓reduceIte, if_true, if_false]
    · intro k hk
      simp only [Function.update_apply]
      have n0 : k ≠ 0#5 := by rintro rfl; simp at hk
      have n8 : k ≠ 8#5 := by rintro rfl; simp at hk
      have n9 : k ≠ 9#5 := by rintro rfl; simp at hk
      have n10 : k ≠ 10#5 := by rintro rfl; simp at hk
      have n11 : k ≠ 11#5 := by rintro rfl; simp at hk
      have n12 : k ≠ 12#5 := by rintro rfl; simp at hk
      simp only [n0, n8, n9, n10, n11, n12, if_false]
  · rw [if_neg hc0] at h'
    refine r_bne_taken (by rw [hz']; simp [hc0]) hrun hW hok2 (f03_684 hCL) ?_ (h' _ ?_ ?_ ?_ ?_)
    · have e3 : BitVec.ofNat 64 684 + 0xffffffffffffffdc#64 = BitVec.ofNat 64 648 := by decide
      rw [BitVec.add_assoc, e3]
    · rw [Function.update_self]; exact e1
    · simp (config := {decide := true}) only [Function.update_apply, ↓reduceIte, if_true, if_false]
      exact h8'
    · simp (config := {decide := true}) only [Function.update_apply, ↓reduceIte, if_true, if_false]
    · intro k hk
      simp only [Function.update_apply]
      have n0 : k ≠ 0#5 := by rintro rfl; simp at hk
      have n8 : k ≠ 8#5 := by rintro rfl; simp at hk
      have n9 : k ≠ 9#5 := by rintro rfl; simp at hk
      have n10 : k ≠ 10#5 := by rintro rfl; simp at hk
      have n11 : k ≠ 11#5 := by rintro rfl; simp at hk
      have n12 : k ≠ 12#5 := by rintro rfl; simp at hk
      simp only [n0, n8, n9, n10, n11, n12, if_false]

theorem set_pre0 (pre : List (BitVec 8)) (b0 b1 X : BitVec 8) (bs : List (BitVec 8)) :
    (pre ++ b0 :: b1 :: bs).set pre.length X = pre ++ X :: b1 :: bs := by
  rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]

theorem set_pre1 (pre : List (BitVec 8)) (X b1 Y : BitVec 8) (bs : List (BitVec 8)) :
    (pre ++ X :: b1 :: bs).set (pre.length + 1) Y = pre ++ X :: Y :: bs := by
  rw [List.set_append_right _ _ (by omega), show pre.length + 1 - pre.length = 1 by omega,
    List.set_cons_succ, List.set_cons_zero]

theorem getD_pre1 (pre : List (BitVec 8)) (b0 b1 : BitVec 8) (bs : List (BitVec 8)) :
    (pre ++ b0 :: b1 :: bs).getD (pre.length + 1) 0#8 = b1 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    show pre.length + 1 - pre.length = 1 by omega]; rfl

/-- All remaining iterations of the loop. -/
theorem loop {mpl : MultiPlacement} {P : State → Prop} {s : State} {sp : BitVec 64} {m0 : Memory}
    {W : BitVec 64 → Prop} (hCL : (prog mpl 3).CodeLoaded m0) (hrun : s.status = .Running)
    (hW : WOwned m0 W) {o : BitVec 64} (hWo : ∀ k, k < 64 → W (o + BitVec.ofNat 64 k))
    (hrd : ∀ k, k < 64 → ∀ m', MemOK m0 W m' → m'.canRead (o + BitVec.ofNat 64 k + 0#64) 1 = true) :
    ∀ (bs pre : List (BitVec 8)) (d : Nat) (b0 b1 : BitVec 8) (r : BitVec 5 → BitVec 64)
      (m : Memory) (ps : PState),
      MemOK m0 W m → OutL m o (pre ++ b0 :: b1 :: bs) → pre.length + bs.length = 62 →
      d ≤ 16 → allNibbles (b1 :: bs) →
      r 0#5 = o + BitVec.ofNat 64 (pre.length + 1) → r 8#5 = BitVec.ofNat 64 (bs.length + 1) →
      r 9#5 = BitVec.ofNat 64 d →
      (∀ r' m' ps', MemOK m0 W m' → OutL m' o (pre ++ recenterNibbles d (b1 :: bs)) →
        (∀ k : BitVec 5, 13 ≤ k.toNat → r' k = r k) →
        Reach mpl 3 P (mkS s (mpl.base 3 + BitVec.ofNat 64 688) r' sp m' ps')) →
      Reach mpl 3 P (mkS s (mpl.base 3 + BitVec.ofNat 64 648) r sp m ps)
  | [], pre, d, b0, b1, r, m, ps, hok, hL, hlen, hd, hnib, h0, h8, h9, h => by
    have hl : (pre ++ b0 :: b1 :: []).length = 64 := by simp; omega
    refine iter hCL hrun hW hok hL hl (by omega) (by simp at hlen; omega) hd
      (by rw [getD_pre1]; exact hnib.1) (by omega) (by omega) hWo h0 h8 h9
      (hrd _ (by simp at hlen; omega)) (fun r' m' ps' hok' hL' h0' h8' h9' hk => ?_)
    simp only [Nat.add_sub_cancel, getD_pre1, set_pre0, set_pre1] at hL'
    simp only [List.length_nil, Nat.zero_add, Nat.sub_self, if_true]
    exact h r' m' ps' hok' (by simpa [recenterNibbles] using hL') hk
  | b2 :: bs, pre, d, b0, b1, r, m, ps, hok, hL, hlen, hd, hnib, h0, h8, h9, h => by
    have hl : (pre ++ b0 :: b1 :: b2 :: bs).length = 64 := by simp at hlen ⊢; omega
    simp only [allNibbles] at hnib
    obtain ⟨hb1, hb2, hnib2⟩ := hnib
    refine iter hCL hrun hW hok hL hl (by omega) (by simp at hlen; omega) hd
      (by rw [getD_pre1]; exact hb1) (by simp) (by simp at hlen ⊢; omega) hWo h0 h8 h9
      (hrd _ (by simp at hlen; omega)) (fun r' m' ps' hok' hL' h0' h8' h9' hk => ?_)
    simp only [Nat.add_sub_cancel, getD_pre1, set_pre0, set_pre1] at hL' h9'
    rw [if_neg (by simp)]
    have hL2 : OutL m' o ((pre ++ [BitVec.ofInt 8 (Int.ofNat d - (Int.ofNat d + 8) / 16 * 16)]) ++
        BitVec.ofNat 8 (b1.toNat + (d + 8) / 16) :: b2 :: bs) := by
      simpa using hL'
    refine loop hCL hrun hW hWo hrd bs _ _ _ b2 r' m' ps' hok' hL2 (by simp at hlen ⊢; omega)
      (by omega) ⟨hb2, hnib2⟩
      (by rw [h0']; simp) (by rw [h8']; simp) h9'
      (fun r2 m2 ps2 hok2 hL3 hk2 => h r2 m2 ps2 hok2 ?_ (fun k hk' => (hk2 k hk').trans (hk k hk')))
    simpa [recenterNibbles] using hL3

end X25519Dalek.EF
end

section
/-! # `Scalar::as_radix_16` (block 3): the straight-line part, offsets 0-644 (generated by
proofs/fnOk_scalar_as_radix_16/tools/gen_phase1.py) -/

namespace X25519Dalek.EF

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Arm64 Arm64.Obj

theorem ze_trunc8 (x : BitVec 8) : ((x.zeroExtend 64 : BitVec 64)).truncate 8 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

/-- The 64 nibbles the straight-line part stores, low nibble first. -/
def nibs (A : List (BitVec 8)) : List (BitVec 8) :=
  [(A.getD 0 0#8 &&& 15#8),
    (A.getD 0 0#8 >>> 4),
    (A.getD 1 0#8 &&& 15#8),
    (A.getD 1 0#8 >>> 4),
    (A.getD 2 0#8 &&& 15#8),
    (A.getD 2 0#8 >>> 4),
    (A.getD 3 0#8 &&& 15#8),
    (A.getD 3 0#8 >>> 4),
    (A.getD 4 0#8 &&& 15#8),
    (A.getD 4 0#8 >>> 4),
    (A.getD 5 0#8 &&& 15#8),
    (A.getD 5 0#8 >>> 4),
    (A.getD 6 0#8 &&& 15#8),
    (A.getD 6 0#8 >>> 4),
    (A.getD 7 0#8 &&& 15#8),
    (A.getD 7 0#8 >>> 4),
    (A.getD 8 0#8 &&& 15#8),
    (A.getD 8 0#8 >>> 4),
    (A.getD 9 0#8 &&& 15#8),
    (A.getD 9 0#8 >>> 4),
    (A.getD 10 0#8 &&& 15#8),
    (A.getD 10 0#8 >>> 4),
    (A.getD 11 0#8 &&& 15#8),
    (A.getD 11 0#8 >>> 4),
    (A.getD 12 0#8 &&& 15#8),
    (A.getD 12 0#8 >>> 4),
    (A.getD 13 0#8 &&& 15#8),
    (A.getD 13 0#8 >>> 4),
    (A.getD 14 0#8 &&& 15#8),
    (A.getD 14 0#8 >>> 4),
    (A.getD 15 0#8 &&& 15#8),
    (A.getD 15 0#8 >>> 4),
    (A.getD 16 0#8 &&& 15#8),
    (A.getD 16 0#8 >>> 4),
    (A.getD 17 0#8 &&& 15#8),
    (A.getD 17 0#8 >>> 4),
    (A.getD 18 0#8 &&& 15#8),
    (A.getD 18 0#8 >>> 4),
    (A.getD 19 0#8 &&& 15#8),
    (A.getD 19 0#8 >>> 4),
    (A.getD 20 0#8 &&& 15#8),
    (A.getD 20 0#8 >>> 4),
    (A.getD 21 0#8 &&& 15#8),
    (A.getD 21 0#8 >>> 4),
    (A.getD 22 0#8 &&& 15#8),
    (A.getD 22 0#8 >>> 4),
    (A.getD 23 0#8 &&& 15#8),
    (A.getD 23 0#8 >>> 4),
    (A.getD 24 0#8 &&& 15#8),
    (A.getD 24 0#8 >>> 4),
    (A.getD 25 0#8 &&& 15#8),
    (A.getD 25 0#8 >>> 4),
    (A.getD 26 0#8 &&& 15#8),
    (A.getD 26 0#8 >>> 4),
    (A.getD 27 0#8 &&& 15#8),
    (A.getD 27 0#8 >>> 4),
    (A.getD 28 0#8 &&& 15#8),
    (A.getD 28 0#8 >>> 4),
    (A.getD 29 0#8 &&& 15#8),
    (A.getD 29 0#8 >>> 4),
    (A.getD 30 0#8 &&& 15#8),
    (A.getD 30 0#8 >>> 4),
    (A.getD 31 0#8 &&& 15#8),
    (A.getD 31 0#8 >>> 4)]

theorem radix_phase1 {mpl : MultiPlacement} {P : State → Prop} {s : State} {sp : BitVec 64}
    {m0 m : Memory} {ps : PState} {W : BitVec 64 → Prop}
    (hCL : (prog mpl 3).CodeLoaded m0) (hrun : s.status = .Running) (hW : WOwned m0 W)
    {a o : BitVec 64} {A : List (BitVec 8)}
    (hrdA : ∀ k, k < 32 → ∀ m', MemOK m0 W m' → m'.read8 (a + BitVec.ofNat 64 k) = A.getD k 0#8)
    (hcrA : ∀ k, k < 32 → ∀ m', MemOK m0 W m' → m'.canRead (a + BitVec.ofNat 64 k) 1 = true)
    (hcrO0 : ∀ m', MemOK m0 W m' → m'.canRead (o + BitVec.ofNat 64 0) 1 = true)
    (hWo : ∀ k, k < 64 → W (o + BitVec.ofNat 64 k))
    (hok : MemOK m0 W m) {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 : BitVec 8}
    (hL : OutL m o [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, x32, x33, x34, x35, x36, x37, x38, x39, x40, x41, x42, x43, x44, x45, x46, x47, x48, x49, x50, x51, x52, x53, x54, x55, x56, x57, x58, x59, x60, x61, x62, x63])
    {q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 q28 q29 q30 q31 : BitVec 64}
    (h : ∀ (L' : List (BitVec 64)) (m' : Memory), MemOK m0 W m' → OutL m' o (nibs A) →
      regL L' 0#5 = o + BitVec.ofNat 64 1 → regL L' 8#5 = (0x003f#16 : BitVec 16).zeroExtend 64 →
      regL L' 9#5 = (A.getD 0 0#8 &&& 15#8).zeroExtend 64 →
      (∀ k : BitVec 5, 13 ≤ k.toNat → regL L' k = regL [o, a, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31] k) →
      Reach mpl 3 P (mkS s (mpl.base 3 + BitVec.ofNat 64 648) (regL L') sp m' ps)) :
    Reach mpl 3 P (mkS s (mpl.base 3 + BitVec.ofNat 64 0) (regL [o, a, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, q29, q30, q31]) sp m ps) := by
  refine r_ldrb (A := a) (k := 0) (by decide) (by decide) hrun hW hok (f03_0 hCL) rfl (hcrA 0 (by decide) _ hok) ?_
  rw [hrdA 0 (by decide) _ hok]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 1) (by decide) (by decide) hrun hW hok (f03_4 hCL) rfl (hcrA 1 (by decide) _ hok) ?_
  rw [hrdA 1 (by decide) _ hok]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_movz (by decide) hrun hW hok (f03_8 hCL) ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 2) (by decide) (by decide) hrun hW hok (f03_12 hCL) rfl (hcrA 2 (by decide) _ hok) ?_
  rw [hrdA 2 (by decide) _ hok]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_and15 (by decide) (by decide) hrun hW hok (f03_16 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 0) (o := o) (by decide) (by decide) hrun hW hok (f03_20 hCL) rfl rfl hL (by simp) (by simp) (hWo 0 (by decide)) (fun m1 hok1 hL1 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL1
  refine r_and15 (by decide) (by decide) hrun hW hok1 (f03_24 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok1 (f03_28 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 2) (o := o) (by decide) (by decide) hrun hW hok1 (f03_32 hCL) rfl rfl hL1 (by simp) (by simp) (hWo 2 (by decide)) (fun m2 hok2 hL2 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL2
  refine r_and15 (by decide) (by decide) hrun hW hok2 (f03_36 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok2 (f03_40 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 4) (o := o) (by decide) (by decide) hrun hW hok2 (f03_44 hCL) rfl rfl hL2 (by simp) (by simp) (hWo 4 (by decide)) (fun m3 hok3 hL3 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL3
  refine r_ldrb (A := a) (k := 3) (by decide) (by decide) hrun hW hok3 (f03_48 hCL) rfl (hcrA 3 (by decide) _ hok3) ?_
  rw [hrdA 3 (by decide) _ hok3]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 3) (o := o) (by decide) (by decide) hrun hW hok3 (f03_52 hCL) rfl rfl hL3 (by simp) (by simp) (hWo 3 (by decide)) (fun m4 hok4 hL4 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL4
  refine r_and15 (by decide) (by decide) hrun hW hok4 (f03_56 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 5) (o := o) (by decide) (by decide) hrun hW hok4 (f03_60 hCL) rfl rfl hL4 (by simp) (by simp) (hWo 5 (by decide)) (fun m5 hok5 hL5 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL5
  refine r_lsr4 (by decide) (by decide) hrun hW hok5 (f03_64 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 6) (o := o) (by decide) (by decide) hrun hW hok5 (f03_68 hCL) rfl rfl hL5 (by simp) (by simp) (hWo 6 (by decide)) (fun m6 hok6 hL6 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL6
  refine r_ldrb (A := a) (k := 4) (by decide) (by decide) hrun hW hok6 (f03_72 hCL) rfl (hcrA 4 (by decide) _ hok6) ?_
  rw [hrdA 4 (by decide) _ hok6]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 5) (by decide) (by decide) hrun hW hok6 (f03_76 hCL) rfl (hcrA 5 (by decide) _ hok6) ?_
  rw [hrdA 5 (by decide) _ hok6]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 7) (o := o) (by decide) (by decide) hrun hW hok6 (f03_80 hCL) rfl rfl hL6 (by simp) (by simp) (hWo 7 (by decide)) (fun m7 hok7 hL7 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL7
  refine r_and15 (by decide) (by decide) hrun hW hok7 (f03_84 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok7 (f03_88 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 8) (o := o) (by decide) (by decide) hrun hW hok7 (f03_92 hCL) rfl rfl hL7 (by simp) (by simp) (hWo 8 (by decide)) (fun m8 hok8 hL8 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL8
  refine r_lsr4 (by decide) (by decide) hrun hW hok8 (f03_96 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 9) (o := o) (by decide) (by decide) hrun hW hok8 (f03_100 hCL) rfl rfl hL8 (by simp) (by simp) (hWo 9 (by decide)) (fun m9 hok9 hL9 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL9
  refine r_and15 (by decide) (by decide) hrun hW hok9 (f03_104 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 7) (by decide) (by decide) hrun hW hok9 (f03_108 hCL) rfl (hcrA 7 (by decide) _ hok9) ?_
  rw [hrdA 7 (by decide) _ hok9]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 10) (o := o) (by decide) (by decide) hrun hW hok9 (f03_112 hCL) rfl rfl hL9 (by simp) (by simp) (hWo 10 (by decide)) (fun m10 hok10 hL10 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL10
  refine r_ldrb (A := a) (k := 6) (by decide) (by decide) hrun hW hok10 (f03_116 hCL) rfl (hcrA 6 (by decide) _ hok10) ?_
  rw [hrdA 6 (by decide) _ hok10]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 11) (o := o) (by decide) (by decide) hrun hW hok10 (f03_120 hCL) rfl rfl hL10 (by simp) (by simp) (hWo 11 (by decide)) (fun m11 hok11 hL11 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL11
  refine r_and15 (by decide) (by decide) hrun hW hok11 (f03_124 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok11 (f03_128 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 12) (o := o) (by decide) (by decide) hrun hW hok11 (f03_132 hCL) rfl rfl hL11 (by simp) (by simp) (hWo 12 (by decide)) (fun m12 hok12 hL12 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL12
  refine r_lsr4 (by decide) (by decide) hrun hW hok12 (f03_136 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 13) (o := o) (by decide) (by decide) hrun hW hok12 (f03_140 hCL) rfl rfl hL12 (by simp) (by simp) (hWo 13 (by decide)) (fun m13 hok13 hL13 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL13
  refine r_and15 (by decide) (by decide) hrun hW hok13 (f03_144 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 9) (by decide) (by decide) hrun hW hok13 (f03_148 hCL) rfl (hcrA 9 (by decide) _ hok13) ?_
  rw [hrdA 9 (by decide) _ hok13]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 14) (o := o) (by decide) (by decide) hrun hW hok13 (f03_152 hCL) rfl rfl hL13 (by simp) (by simp) (hWo 14 (by decide)) (fun m14 hok14 hL14 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL14
  refine r_ldrb (A := a) (k := 8) (by decide) (by decide) hrun hW hok14 (f03_156 hCL) rfl (hcrA 8 (by decide) _ hok14) ?_
  rw [hrdA 8 (by decide) _ hok14]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 15) (o := o) (by decide) (by decide) hrun hW hok14 (f03_160 hCL) rfl rfl hL14 (by simp) (by simp) (hWo 15 (by decide)) (fun m15 hok15 hL15 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL15
  refine r_and15 (by decide) (by decide) hrun hW hok15 (f03_164 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok15 (f03_168 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 16) (o := o) (by decide) (by decide) hrun hW hok15 (f03_172 hCL) rfl rfl hL15 (by simp) (by simp) (hWo 16 (by decide)) (fun m16 hok16 hL16 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL16
  refine r_lsr4 (by decide) (by decide) hrun hW hok16 (f03_176 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 17) (o := o) (by decide) (by decide) hrun hW hok16 (f03_180 hCL) rfl rfl hL16 (by simp) (by simp) (hWo 17 (by decide)) (fun m17 hok17 hL17 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL17
  refine r_and15 (by decide) (by decide) hrun hW hok17 (f03_184 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 11) (by decide) (by decide) hrun hW hok17 (f03_188 hCL) rfl (hcrA 11 (by decide) _ hok17) ?_
  rw [hrdA 11 (by decide) _ hok17]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 18) (o := o) (by decide) (by decide) hrun hW hok17 (f03_192 hCL) rfl rfl hL17 (by simp) (by simp) (hWo 18 (by decide)) (fun m18 hok18 hL18 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL18
  refine r_ldrb (A := a) (k := 10) (by decide) (by decide) hrun hW hok18 (f03_196 hCL) rfl (hcrA 10 (by decide) _ hok18) ?_
  rw [hrdA 10 (by decide) _ hok18]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 19) (o := o) (by decide) (by decide) hrun hW hok18 (f03_200 hCL) rfl rfl hL18 (by simp) (by simp) (hWo 19 (by decide)) (fun m19 hok19 hL19 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL19
  refine r_and15 (by decide) (by decide) hrun hW hok19 (f03_204 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok19 (f03_208 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 20) (o := o) (by decide) (by decide) hrun hW hok19 (f03_212 hCL) rfl rfl hL19 (by simp) (by simp) (hWo 20 (by decide)) (fun m20 hok20 hL20 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL20
  refine r_lsr4 (by decide) (by decide) hrun hW hok20 (f03_216 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 21) (o := o) (by decide) (by decide) hrun hW hok20 (f03_220 hCL) rfl rfl hL20 (by simp) (by simp) (hWo 21 (by decide)) (fun m21 hok21 hL21 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL21
  refine r_and15 (by decide) (by decide) hrun hW hok21 (f03_224 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 13) (by decide) (by decide) hrun hW hok21 (f03_228 hCL) rfl (hcrA 13 (by decide) _ hok21) ?_
  rw [hrdA 13 (by decide) _ hok21]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 22) (o := o) (by decide) (by decide) hrun hW hok21 (f03_232 hCL) rfl rfl hL21 (by simp) (by simp) (hWo 22 (by decide)) (fun m22 hok22 hL22 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL22
  refine r_ldrb (A := a) (k := 12) (by decide) (by decide) hrun hW hok22 (f03_236 hCL) rfl (hcrA 12 (by decide) _ hok22) ?_
  rw [hrdA 12 (by decide) _ hok22]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 23) (o := o) (by decide) (by decide) hrun hW hok22 (f03_240 hCL) rfl rfl hL22 (by simp) (by simp) (hWo 23 (by decide)) (fun m23 hok23 hL23 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL23
  refine r_and15 (by decide) (by decide) hrun hW hok23 (f03_244 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok23 (f03_248 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 24) (o := o) (by decide) (by decide) hrun hW hok23 (f03_252 hCL) rfl rfl hL23 (by simp) (by simp) (hWo 24 (by decide)) (fun m24 hok24 hL24 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL24
  refine r_lsr4 (by decide) (by decide) hrun hW hok24 (f03_256 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 25) (o := o) (by decide) (by decide) hrun hW hok24 (f03_260 hCL) rfl rfl hL24 (by simp) (by simp) (hWo 25 (by decide)) (fun m25 hok25 hL25 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL25
  refine r_and15 (by decide) (by decide) hrun hW hok25 (f03_264 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 15) (by decide) (by decide) hrun hW hok25 (f03_268 hCL) rfl (hcrA 15 (by decide) _ hok25) ?_
  rw [hrdA 15 (by decide) _ hok25]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 26) (o := o) (by decide) (by decide) hrun hW hok25 (f03_272 hCL) rfl rfl hL25 (by simp) (by simp) (hWo 26 (by decide)) (fun m26 hok26 hL26 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL26
  refine r_ldrb (A := a) (k := 14) (by decide) (by decide) hrun hW hok26 (f03_276 hCL) rfl (hcrA 14 (by decide) _ hok26) ?_
  rw [hrdA 14 (by decide) _ hok26]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 27) (o := o) (by decide) (by decide) hrun hW hok26 (f03_280 hCL) rfl rfl hL26 (by simp) (by simp) (hWo 27 (by decide)) (fun m27 hok27 hL27 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL27
  refine r_and15 (by decide) (by decide) hrun hW hok27 (f03_284 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok27 (f03_288 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 28) (o := o) (by decide) (by decide) hrun hW hok27 (f03_292 hCL) rfl rfl hL27 (by simp) (by simp) (hWo 28 (by decide)) (fun m28 hok28 hL28 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL28
  refine r_lsr4 (by decide) (by decide) hrun hW hok28 (f03_296 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 29) (o := o) (by decide) (by decide) hrun hW hok28 (f03_300 hCL) rfl rfl hL28 (by simp) (by simp) (hWo 29 (by decide)) (fun m29 hok29 hL29 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL29
  refine r_and15 (by decide) (by decide) hrun hW hok29 (f03_304 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 17) (by decide) (by decide) hrun hW hok29 (f03_308 hCL) rfl (hcrA 17 (by decide) _ hok29) ?_
  rw [hrdA 17 (by decide) _ hok29]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 30) (o := o) (by decide) (by decide) hrun hW hok29 (f03_312 hCL) rfl rfl hL29 (by simp) (by simp) (hWo 30 (by decide)) (fun m30 hok30 hL30 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL30
  refine r_ldrb (A := a) (k := 16) (by decide) (by decide) hrun hW hok30 (f03_316 hCL) rfl (hcrA 16 (by decide) _ hok30) ?_
  rw [hrdA 16 (by decide) _ hok30]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 31) (o := o) (by decide) (by decide) hrun hW hok30 (f03_320 hCL) rfl rfl hL30 (by simp) (by simp) (hWo 31 (by decide)) (fun m31 hok31 hL31 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL31
  refine r_and15 (by decide) (by decide) hrun hW hok31 (f03_324 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok31 (f03_328 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 32) (o := o) (by decide) (by decide) hrun hW hok31 (f03_332 hCL) rfl rfl hL31 (by simp) (by simp) (hWo 32 (by decide)) (fun m32 hok32 hL32 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL32
  refine r_lsr4 (by decide) (by decide) hrun hW hok32 (f03_336 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 33) (o := o) (by decide) (by decide) hrun hW hok32 (f03_340 hCL) rfl rfl hL32 (by simp) (by simp) (hWo 33 (by decide)) (fun m33 hok33 hL33 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL33
  refine r_and15 (by decide) (by decide) hrun hW hok33 (f03_344 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 19) (by decide) (by decide) hrun hW hok33 (f03_348 hCL) rfl (hcrA 19 (by decide) _ hok33) ?_
  rw [hrdA 19 (by decide) _ hok33]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 34) (o := o) (by decide) (by decide) hrun hW hok33 (f03_352 hCL) rfl rfl hL33 (by simp) (by simp) (hWo 34 (by decide)) (fun m34 hok34 hL34 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL34
  refine r_ldrb (A := a) (k := 18) (by decide) (by decide) hrun hW hok34 (f03_356 hCL) rfl (hcrA 18 (by decide) _ hok34) ?_
  rw [hrdA 18 (by decide) _ hok34]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 35) (o := o) (by decide) (by decide) hrun hW hok34 (f03_360 hCL) rfl rfl hL34 (by simp) (by simp) (hWo 35 (by decide)) (fun m35 hok35 hL35 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL35
  refine r_and15 (by decide) (by decide) hrun hW hok35 (f03_364 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok35 (f03_368 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 36) (o := o) (by decide) (by decide) hrun hW hok35 (f03_372 hCL) rfl rfl hL35 (by simp) (by simp) (hWo 36 (by decide)) (fun m36 hok36 hL36 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL36
  refine r_lsr4 (by decide) (by decide) hrun hW hok36 (f03_376 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 37) (o := o) (by decide) (by decide) hrun hW hok36 (f03_380 hCL) rfl rfl hL36 (by simp) (by simp) (hWo 37 (by decide)) (fun m37 hok37 hL37 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL37
  refine r_and15 (by decide) (by decide) hrun hW hok37 (f03_384 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 21) (by decide) (by decide) hrun hW hok37 (f03_388 hCL) rfl (hcrA 21 (by decide) _ hok37) ?_
  rw [hrdA 21 (by decide) _ hok37]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 38) (o := o) (by decide) (by decide) hrun hW hok37 (f03_392 hCL) rfl rfl hL37 (by simp) (by simp) (hWo 38 (by decide)) (fun m38 hok38 hL38 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL38
  refine r_ldrb (A := a) (k := 20) (by decide) (by decide) hrun hW hok38 (f03_396 hCL) rfl (hcrA 20 (by decide) _ hok38) ?_
  rw [hrdA 20 (by decide) _ hok38]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 39) (o := o) (by decide) (by decide) hrun hW hok38 (f03_400 hCL) rfl rfl hL38 (by simp) (by simp) (hWo 39 (by decide)) (fun m39 hok39 hL39 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL39
  refine r_and15 (by decide) (by decide) hrun hW hok39 (f03_404 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok39 (f03_408 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 40) (o := o) (by decide) (by decide) hrun hW hok39 (f03_412 hCL) rfl rfl hL39 (by simp) (by simp) (hWo 40 (by decide)) (fun m40 hok40 hL40 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL40
  refine r_lsr4 (by decide) (by decide) hrun hW hok40 (f03_416 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 41) (o := o) (by decide) (by decide) hrun hW hok40 (f03_420 hCL) rfl rfl hL40 (by simp) (by simp) (hWo 41 (by decide)) (fun m41 hok41 hL41 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL41
  refine r_and15 (by decide) (by decide) hrun hW hok41 (f03_424 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 23) (by decide) (by decide) hrun hW hok41 (f03_428 hCL) rfl (hcrA 23 (by decide) _ hok41) ?_
  rw [hrdA 23 (by decide) _ hok41]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 42) (o := o) (by decide) (by decide) hrun hW hok41 (f03_432 hCL) rfl rfl hL41 (by simp) (by simp) (hWo 42 (by decide)) (fun m42 hok42 hL42 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL42
  refine r_ldrb (A := a) (k := 22) (by decide) (by decide) hrun hW hok42 (f03_436 hCL) rfl (hcrA 22 (by decide) _ hok42) ?_
  rw [hrdA 22 (by decide) _ hok42]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 43) (o := o) (by decide) (by decide) hrun hW hok42 (f03_440 hCL) rfl rfl hL42 (by simp) (by simp) (hWo 43 (by decide)) (fun m43 hok43 hL43 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL43
  refine r_and15 (by decide) (by decide) hrun hW hok43 (f03_444 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok43 (f03_448 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 44) (o := o) (by decide) (by decide) hrun hW hok43 (f03_452 hCL) rfl rfl hL43 (by simp) (by simp) (hWo 44 (by decide)) (fun m44 hok44 hL44 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL44
  refine r_lsr4 (by decide) (by decide) hrun hW hok44 (f03_456 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 45) (o := o) (by decide) (by decide) hrun hW hok44 (f03_460 hCL) rfl rfl hL44 (by simp) (by simp) (hWo 45 (by decide)) (fun m45 hok45 hL45 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL45
  refine r_and15 (by decide) (by decide) hrun hW hok45 (f03_464 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 25) (by decide) (by decide) hrun hW hok45 (f03_468 hCL) rfl (hcrA 25 (by decide) _ hok45) ?_
  rw [hrdA 25 (by decide) _ hok45]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 46) (o := o) (by decide) (by decide) hrun hW hok45 (f03_472 hCL) rfl rfl hL45 (by simp) (by simp) (hWo 46 (by decide)) (fun m46 hok46 hL46 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL46
  refine r_ldrb (A := a) (k := 24) (by decide) (by decide) hrun hW hok46 (f03_476 hCL) rfl (hcrA 24 (by decide) _ hok46) ?_
  rw [hrdA 24 (by decide) _ hok46]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 47) (o := o) (by decide) (by decide) hrun hW hok46 (f03_480 hCL) rfl rfl hL46 (by simp) (by simp) (hWo 47 (by decide)) (fun m47 hok47 hL47 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL47
  refine r_and15 (by decide) (by decide) hrun hW hok47 (f03_484 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok47 (f03_488 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 48) (o := o) (by decide) (by decide) hrun hW hok47 (f03_492 hCL) rfl rfl hL47 (by simp) (by simp) (hWo 48 (by decide)) (fun m48 hok48 hL48 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL48
  refine r_lsr4 (by decide) (by decide) hrun hW hok48 (f03_496 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 49) (o := o) (by decide) (by decide) hrun hW hok48 (f03_500 hCL) rfl rfl hL48 (by simp) (by simp) (hWo 49 (by decide)) (fun m49 hok49 hL49 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL49
  refine r_and15 (by decide) (by decide) hrun hW hok49 (f03_504 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 27) (by decide) (by decide) hrun hW hok49 (f03_508 hCL) rfl (hcrA 27 (by decide) _ hok49) ?_
  rw [hrdA 27 (by decide) _ hok49]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 50) (o := o) (by decide) (by decide) hrun hW hok49 (f03_512 hCL) rfl rfl hL49 (by simp) (by simp) (hWo 50 (by decide)) (fun m50 hok50 hL50 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL50
  refine r_ldrb (A := a) (k := 26) (by decide) (by decide) hrun hW hok50 (f03_516 hCL) rfl (hcrA 26 (by decide) _ hok50) ?_
  rw [hrdA 26 (by decide) _ hok50]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 51) (o := o) (by decide) (by decide) hrun hW hok50 (f03_520 hCL) rfl rfl hL50 (by simp) (by simp) (hWo 51 (by decide)) (fun m51 hok51 hL51 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL51
  refine r_and15 (by decide) (by decide) hrun hW hok51 (f03_524 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok51 (f03_528 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 52) (o := o) (by decide) (by decide) hrun hW hok51 (f03_532 hCL) rfl rfl hL51 (by simp) (by simp) (hWo 52 (by decide)) (fun m52 hok52 hL52 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL52
  refine r_lsr4 (by decide) (by decide) hrun hW hok52 (f03_536 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 53) (o := o) (by decide) (by decide) hrun hW hok52 (f03_540 hCL) rfl rfl hL52 (by simp) (by simp) (hWo 53 (by decide)) (fun m53 hok53 hL53 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL53
  refine r_and15 (by decide) (by decide) hrun hW hok53 (f03_544 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 29) (by decide) (by decide) hrun hW hok53 (f03_548 hCL) rfl (hcrA 29 (by decide) _ hok53) ?_
  rw [hrdA 29 (by decide) _ hok53]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 54) (o := o) (by decide) (by decide) hrun hW hok53 (f03_552 hCL) rfl rfl hL53 (by simp) (by simp) (hWo 54 (by decide)) (fun m54 hok54 hL54 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL54
  refine r_ldrb (A := a) (k := 28) (by decide) (by decide) hrun hW hok54 (f03_556 hCL) rfl (hcrA 28 (by decide) _ hok54) ?_
  rw [hrdA 28 (by decide) _ hok54]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 55) (o := o) (by decide) (by decide) hrun hW hok54 (f03_560 hCL) rfl rfl hL54 (by simp) (by simp) (hWo 55 (by decide)) (fun m55 hok55 hL55 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL55
  refine r_and15 (by decide) (by decide) hrun hW hok55 (f03_564 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok55 (f03_568 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 56) (o := o) (by decide) (by decide) hrun hW hok55 (f03_572 hCL) rfl rfl hL55 (by simp) (by simp) (hWo 56 (by decide)) (fun m56 hok56 hL56 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL56
  refine r_lsr4 (by decide) (by decide) hrun hW hok56 (f03_576 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 57) (o := o) (by decide) (by decide) hrun hW hok56 (f03_580 hCL) rfl rfl hL56 (by simp) (by simp) (hWo 57 (by decide)) (fun m57 hok57 hL57 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL57
  refine r_and15 (by decide) (by decide) hrun hW hok57 (f03_584 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := a) (k := 31) (by decide) (by decide) hrun hW hok57 (f03_588 hCL) rfl (hcrA 31 (by decide) _ hok57) ?_
  rw [hrdA 31 (by decide) _ hok57]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 58) (o := o) (by decide) (by decide) hrun hW hok57 (f03_592 hCL) rfl rfl hL57 (by simp) (by simp) (hWo 58 (by decide)) (fun m58 hok58 hL58 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL58
  refine r_ldrb (A := a) (k := 30) (by decide) (by decide) hrun hW hok58 (f03_596 hCL) rfl (hcrA 30 (by decide) _ hok58) ?_
  rw [hrdA 30 (by decide) _ hok58]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 59) (o := o) (by decide) (by decide) hrun hW hok58 (f03_600 hCL) rfl rfl hL58 (by simp) (by simp) (hWo 59 (by decide)) (fun m59 hok59 hL59 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL59
  refine r_and15 (by decide) (by decide) hrun hW hok59 (f03_604 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok59 (f03_608 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 60) (o := o) (by decide) (by decide) hrun hW hok59 (f03_612 hCL) rfl rfl hL59 (by simp) (by simp) (hWo 60 (by decide)) (fun m60 hok60 hL60 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL60
  refine r_lsr4 (by decide) (by decide) hrun hW hok60 (f03_616 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 61) (o := o) (by decide) (by decide) hrun hW hok60 (f03_620 hCL) rfl rfl hL60 (by simp) (by simp) (hWo 61 (by decide)) (fun m61 hok61 hL61 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL61
  refine r_and15 (by decide) (by decide) hrun hW hok61 (f03_624 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_lsr4 (by decide) (by decide) hrun hW hok61 (f03_628 hCL) rfl ?_
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_ldrb (A := o) (k := 0) (by decide) (by decide) hrun hW hok61 (f03_632 hCL) rfl (hcrO0 _ hok61) ?_
  rw [hL61 0 (by simp)]
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine r_strbO (j := 62) (o := o) (by decide) (by decide) hrun hW hok61 (f03_636 hCL) rfl rfl hL61 (by simp) (by simp) (hWo 62 (by decide)) (fun m62 hok62 hL62 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL62
  refine r_strbO (j := 63) (o := o) (by decide) (by decide) hrun hW hok62 (f03_640 hCL) rfl rfl hL62 (by simp) (by simp) (hWo 63 (by decide)) (fun m63 hok63 hL63 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL63
  refine r_strb_preO (j := 1) (o := o) (by decide) (by decide) hrun hW hok63 (f03_644 hCL) rfl rfl (ze_trunc8 _) hL63 (by simp) (by simp) (hWo 1 (by decide)) (fun m64 hok64 hL64 => ?_)
  simp only [List.set_cons_succ, List.set_cons_zero] at hL64
  simp only [regL_update, regL_get, List.set_cons_succ, List.set_cons_zero, List.getD_cons_succ, List.getD_cons_zero, List.length_cons, List.length_nil, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd]
  refine h _ _ hok64 hL64 rfl rfl rfl ?_
  intro k hk
  simp only [regL_get]
  have hk2 : k.toNat < 32 := k.isLt
  generalize k.toNat = j at hk hk2
  interval_cases j <;> rfl

end X25519Dalek.EF
end

section
/-! # Owned byte lists: their cells, values and permissions -/

namespace X25519Dalek.EF

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

theorem bytes_phys : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap), (a ↦ₛ bs).holds h →
    bs.length < 2 ^ 64 → ∀ k (hk : k < bs.length), h.phys (a + BitVec.ofNat 64 k) = some (.rw bs[k])
  | [], _, _, _, _, k, hk => by simp at hk
  | b :: bs, a, h, hh, hl, k, hk => by
    simp only [pointsToBytes] at hh
    obtain ⟨h1, h2, hd, rfl, p1, p2⟩ := hh
    change h1 = Heap.singleton a b at p1
    subst p1
    rcases k with _ | k
    · simp [Heap.union, Heap.singleton]
    · have ih := bytes_phys bs (a + 1#64) h2 p2 (by simp at hl; omega) k (by simp at hk; omega)
      have e : a + BitVec.ofNat 64 (k + 1) = a + 1#64 + BitVec.ofNat 64 k := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have hne : a + BitVec.ofNat 64 (k + 1) ≠ a := by
        intro e2
        have h3 := congrArg BitVec.toNat e2
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h3
        simp only [List.length_cons] at hk hl
        have ha := a.isLt
        rw [Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64)] at h3
        omega
      simp only [Heap.union, Heap.singleton, if_neg hne, List.getElem_cons_succ]
      rw [e]; exact ih

/-- The bytes of an owned list, under a frame: values, permissions, and that a set owned by the
frame does not contain them. -/
theorem sat_bytes_facts {a : BitVec 64} {bs : List (BitVec 8)} {Q R : SepProp} {m : Memory}
    {W : BitVec 64 → Prop} (hs : m ⊨ ((a ↦ₛ bs) ∗ Q) ∗ R) (hQ : OwnsRW Q W) (hl : bs.length < 2 ^ 64)
    (k : Nat) (hk : k < bs.length) :
    m.read8 (a + BitVec.ofNat 64 k) = bs[k] ∧ m.perm (a + BitVec.ofNat 64 k) = some Perm.rw ∧
      m.isLazyFree (a + BitVec.ofNat 64 k) = false ∧ ¬ W (a + BitVec.ofNat 64 k) := by
  obtain ⟨_, ⟨hP, hR, hd, rfl, p, _⟩, hm⟩ := hs
  have hph := p
  obtain ⟨h1, h2, _, rfl, p1, _⟩ := hph
  have e1 := bytes_phys bs a h1 p1 hl k hk
  have eu : ((h1.union h2).union hR).phys (a + BitVec.ofNat 64 k) = some (HeapCell.rw bs[k]) := by
    simp [Heap.union, e1]
  obtain ⟨r1, r2, r3⟩ := hm.1 _ _ eu
  exact ⟨r1, r2, r3, not_W_of p hQ (fun h1' p1' => by rw [bytes_phys bs a h1' p1' hl k hk]; simp)⟩

end X25519Dalek.EF
end

section
/-! # `Scalar::as_radix_16` (block 3, 173 instructions): the contract

Route: google-deepmind/code-verification @ 8c8d371f (Apache-2.0), `Shared51/ScalarRadix16.lean`
(`scalar_as_radix_16_ok`), re-proved with plain tactics on the xd-field batch's framework. -/

namespace X25519Dalek.EF

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

theorem list64 (L : List (BitVec 8)) (h : L.length = 64) :
    L = [L.getD 0 0#8, L.getD 1 0#8, L.getD 2 0#8, L.getD 3 0#8, L.getD 4 0#8, L.getD 5 0#8, L.getD 6 0#8, L.getD 7 0#8, L.getD 8 0#8, L.getD 9 0#8, L.getD 10 0#8, L.getD 11 0#8, L.getD 12 0#8, L.getD 13 0#8, L.getD 14 0#8, L.getD 15 0#8, L.getD 16 0#8, L.getD 17 0#8, L.getD 18 0#8, L.getD 19 0#8, L.getD 20 0#8, L.getD 21 0#8, L.getD 22 0#8, L.getD 23 0#8, L.getD 24 0#8, L.getD 25 0#8, L.getD 26 0#8, L.getD 27 0#8, L.getD 28 0#8, L.getD 29 0#8, L.getD 30 0#8, L.getD 31 0#8, L.getD 32 0#8, L.getD 33 0#8, L.getD 34 0#8, L.getD 35 0#8, L.getD 36 0#8, L.getD 37 0#8, L.getD 38 0#8, L.getD 39 0#8, L.getD 40 0#8, L.getD 41 0#8, L.getD 42 0#8, L.getD 43 0#8, L.getD 44 0#8, L.getD 45 0#8, L.getD 46 0#8, L.getD 47 0#8, L.getD 48 0#8, L.getD 49 0#8, L.getD 50 0#8, L.getD 51 0#8, L.getD 52 0#8, L.getD 53 0#8, L.getD 54 0#8, L.getD 55 0#8, L.getD 56 0#8, L.getD 57 0#8, L.getD 58 0#8, L.getD 59 0#8, L.getD 60 0#8, L.getD 61 0#8, L.getD 62 0#8, L.getD 63 0#8] := by
  rcases L with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp at h <;> rfl

theorem nib_lt (b : BitVec 8) : (b &&& 15#8).toNat < 16 ∧ (b >>> 4).toNat < 16 := by
  revert b; decide

theorem bytesAt_eq {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)}
    (h : ∀ i (hi : i < bs.length), m.read8 (a + BitVec.ofNat 64 i) = bs[i]) :
    bytesAt m a bs.length = bs := by
  apply List.ext_getElem (bytesAt_length _ _ _)
  intro i h1 h2
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  exact h i h2

theorem recenterNibbles_length : ∀ (L : List (BitVec 8)) (d : Nat),
    (recenterNibbles d L).length = L.length + 1
  | [], _ => rfl
  | _ :: L, _ => by simp [recenterNibbles, recenterNibbles_length L]

theorem digits_eq (A : List (BitVec 8)) :
    [] ++ recenterNibbles (A.getD 0 0#8 &&& 15#8).toNat (A.getD 0 0#8 >>> 4 :: List.drop 2 (nibs A)) =
      scalarRadix16Digits A := by
  rw [scalarRadix16Digits_eq_recenterNibbles, List.nil_append]
  congr 1

theorem sepConj_true_left (P : SepProp) : (⌜True⌝ ∗ P) = P := by
  rw [sepConj_comm, sepConj_pure_true]

theorem fnOk_scalar_as_radix_16_dev :
    fnOk "<curve25519_dalek::scalar::Scalar>::as_radix_16" (fun _ => scalarAsRadix16Spec) := by
  refine ⟨3, 0, rfl, fun mpl _ => ?_⟩
  rintro ⟨out, a, out_bs, a_bs⟩ R s0 hpc hrun hpre hal hCL
  have hfa : x25519CliMultiLib.fnAddr mpl "<curve25519_dalek::scalar::Scalar>::as_radix_16" =
      mpl.base 3 + BitVec.ofNat 64 0 := rfl
  rw [hfa] at hpc
  change s0.mem ⊨ ((⌜s0.readReg64 Reg.x0 = out ∧ s0.readReg64 Reg.x1 = a ∧ out_bs.length = 64 ∧
      a_bs.length = 32 ∧ (a_bs.getD 31 0#8).toNat ≤ 127⌝ ∗ ((a ↦ₛ a_bs) ∗ (out ↦ₛ out_bs))) ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝) ∗ R at hpre
  have hφ := pure_of_sat (P := (a ↦ₛ a_bs) ∗ (out ↦ₛ out_bs)) (by rw [sepConj_assoc] at hpre; exact hpre)
  obtain ⟨hx0, hx1, hlo, hla, -⟩ := hφ
  set W : BitVec 64 → Prop := InRegion out 64 with hWdef
  have hOwnQ : OwnsRW (out ↦ₛ out_bs) W := by
    have := ownsRW_bytes out_bs out; rwa [hlo] at this
  have hOwnPre : OwnsRW ((⌜s0.readReg64 Reg.x0 = out ∧ s0.readReg64 Reg.x1 = a ∧ out_bs.length = 64 ∧
      a_bs.length = 32 ∧ (a_bs.getD 31 0#8).toNat ≤ 127⌝ ∗ ((a ↦ₛ a_bs) ∗ (out ↦ₛ out_bs))) ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝) W :=
    ownsRW_sep_left (ownsRW_sep_right (ownsRW_sep_right hOwnQ))
  have hW := wowned_of hpre hOwnPre
  have hs : s0.mem ⊨ ((a ↦ₛ a_bs) ∗ (out ↦ₛ out_bs)) ∗ ((⌜s0.readReg64 Reg.x0 = out ∧
      s0.readReg64 Reg.x1 = a ∧ out_bs.length = 64 ∧ a_bs.length = 32 ∧
      (a_bs.getD 31 0#8).toNat ≤ 127⌝) ∗ (⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝ ∗ R)) := by
    rw [sepConj_assoc, sepConj_assoc, sepConj_left_comm] at hpre; exact hpre
  have hs2 : s0.mem ⊨ ((out ↦ₛ out_bs) ∗ (a ↦ₛ a_bs)) ∗ ((⌜s0.readReg64 Reg.x0 = out ∧
      s0.readReg64 Reg.x1 = a ∧ out_bs.length = 64 ∧ a_bs.length = 32 ∧
      (a_bs.getD 31 0#8).toNat ≤ 127⌝) ∗ (⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝ ∗ R)) := by
    rw [sepConj_comm (out ↦ₛ out_bs)]; exact hs
  have fA := fun k (hk : k < a_bs.length) => sat_bytes_facts hs hOwnQ (by omega) k hk
  have fO := fun k (hk : k < out_bs.length) =>
    sat_bytes_facts (W := fun _ => False) hs2 (fun _ _ _ hx => hx.elim) (by omega) k hk
  have hrdA : ∀ k, k < 32 → ∀ m', MemOK s0.mem W m' →
      m'.read8 (a + BitVec.ofNat 64 k) = a_bs.getD k 0#8 := by
    intro k hk m' hok
    rw [(hok _).2.2.2 (fA k (by omega)).2.2.2, (fA k (by omega)).1, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]; rfl
  have hcrA : ∀ k, k < 32 → ∀ m', MemOK s0.mem W m' → m'.canRead (a + BitVec.ofNat 64 k) 1 = true := by
    intro k hk m' hok
    refine canRead_of hok fun j hj => ?_
    have : j = 0 := by omega
    subst this
    simp only [BitVec.add_zero]
    have := fA k (by omega)
    exact ⟨by rw [this.2.1]; rfl, this.2.2.1⟩
  have hWo : ∀ k, k < 64 → W (out + BitVec.ofNat 64 k) := by
    intro k hk
    show ((out + BitVec.ofNat 64 k) - out).toNat < 64
    rw [BitVec.add_comm out, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hk
  have hcrO : ∀ k, k < 64 → ∀ m', MemOK s0.mem W m' →
      m'.canRead (out + BitVec.ofNat 64 k + 0#64) 1 = true := by
    intro k hk m' hok
    refine canRead_of_W hW hok fun j hj => ?_
    have : j = 0 := by omega
    subst this
    simpa using hWo k hk
  have hcrO0 : ∀ m', MemOK s0.mem W m' → m'.canRead (out + BitVec.ofNat 64 0) 1 = true := by
    intro m' hok; simpa using hcrO 0 (by omega) m' hok
  have hxs := list64 out_bs hlo
  have hL0' : OutL s0.mem out out_bs := by
    intro k hk
    rw [(fO k hk).1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  rw [hxs] at hL0'
  have ha : s0.regs.regs 1#5 = a := by simpa [State.readReg64, RegFile.read] using hx1
  have ho : s0.regs.regs 0#5 = out := by simpa [State.readReg64, RegFile.read] using hx0
  show Reach mpl 3 _ s0
  apply reach_start
  rw [hpc, regL_init s0.regs.regs, ho, ha]
  refine radix_phase1 hCL hrun hW hrdA hcrA hcrO0 hWo (memOK_refl _ _) hL0' ?_
  intro L' m1 hok1 hL1 h0 h8 h9 hk1
  have hn := nib_lt (a_bs.getD 0 0#8)
  refine loop hCL hrun hW hWo hcrO (List.drop 2 (nibs a_bs)) [] (a_bs.getD 0 0#8 &&& 15#8).toNat
    (a_bs.getD 0 0#8 &&& 15#8) (a_bs.getD 0 0#8 >>> 4) (regL L') m1 _ hok1 hL1 rfl (by omega)
    ?_ h0 (by rw [h8]; rfl) (by rw [h9, ze_byte]) ?_
  · simp only [nibs, List.drop, allNibbles]
    simp only [nib_lt, and_self, and_true, true_and]
  intro r2 m2 ps2 hok2 hL2 hk2
  refine r_ret hrun hW hok2 (f03_688 hCL) ?_
  have hr30 : r2 30#5 = s0.regs.regs 30#5 := by
    rw [hk2 30#5 (by decide), hk1 30#5 (by decide)]; rfl
  rw [hr30]
  have hcal : ∀ k : BitVec 5, 19 ≤ k.toNat → r2 k = s0.regs.regs k := by
    intro k hk
    rw [hk2 k (by omega), hk1 k (by omega), regL_get, regL_init s0.regs.regs, regL_get]
    have hk3 : k.toNat < 32 := k.isLt
    simp only [ho, ha]
    have e : k = BitVec.ofNat 5 k.toNat := by simp
    generalize hj : k.toNat = j at hk hk3 e
    subst e
    interval_cases j <;> rfl
  refine outcome_of hrun hcal (frame hpre hok2 hOwnPre (rf_mono (rf_sep (rf_sep (rf_pure' (ψ := True)
    (fun _ => trivial)) (rf_sep (rf_bytes m2 a_bs a) (rf_bytes m2 out_bs out))) (rf_pure' (fun _ => trivial))) ?_))
  rw [sepConj_pure_true, sepConj_true_left]
  have eA : bytesAt m2 a a_bs.length = a_bs := bytesAt_eq fun i hi => by
    rw [(hok2 _).2.2.2 (fA i hi).2.2.2, (fA i hi).1]
  have eO : bytesAt m2 out out_bs.length = scalarRadix16Digits a_bs := by
    rw [← digits_eq, hlo]
    have hl : ([] ++ recenterNibbles (a_bs.getD 0 0#8 &&& 15#8).toNat
        (a_bs.getD 0 0#8 >>> 4 :: List.drop 2 (nibs a_bs))).length = 64 := by
      rw [List.nil_append, recenterNibbles_length]; simp [nibs]
    rw [← hl]
    exact bytesAt_eq fun i hi => by
      rw [hL2 i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  rw [eA, eO]
  intro h hh; exact hh

end X25519Dalek.EF
end

open X25519Dalek in
theorem solution :
    fnOk
      "<curve25519_dalek::scalar::Scalar>::as_radix_16"
      (fun _ => scalarAsRadix16Spec) :=
  X25519Dalek.EF.fnOk_scalar_as_radix_16_dev
