-- Prove2me | solution 1 for Poly1305DebianCt.oneshot_guard_reloc_decode
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-26T20:55:50.16793+00:00
-- url     : https://prove2.me/submissions/73d5d11c-278f-4961-b1a3-458e65935dea

import Definitions.Def_Poly1305DebianCt_PlacedObj
import Definitions.Def_Poly1305DebianCt_Spec
import Mathlib.Tactic.IntervalCases
import Definitions.Def_Arm64_Leakage
import Definitions.Def_Arm64_ISA_Semantics
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
theorem holds_emp_iff {h : Heap} : (emp : SepProp).holds h ↔ h = Heap.empty := Iff.rfl
theorem holds_sepConj_iff {P Q : SepProp} {h : Heap} :
    (P ∗ Q).holds h ↔
      ∃ h₁ h₂ : Heap, h₁.Disjoint h₂ ∧ h = h₁.union h₂ ∧ P.holds h₁ ∧ Q.holds h₂ := Iff.rfl
end SepProp

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

end Heap











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

namespace Heap

end Heap

/-! ## Memory facts about `write8` -/

namespace Memory

end Memory

namespace Heap

end Heap

/-! ## Byte slices as heaps -/

/-! ## Satisfaction-level reads and writes -/

/-! ## Splitting byte slices -/

/-- Unpack a 64-bit word into its 8 little-endian bytes. -/
def unpack64 (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
   v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8]

@[simp] theorem unpack64_length (v : BitVec 64) : (unpack64 v).length = 8 := rfl

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

/-! ## Byte-slice heaps carry no ghost state and nothing outside the slice -/

end Arm64

end
end

section
section
/-! # 64-bit cells and byte reads: values and permissions from ownership -/

set_option autoImplicit false

namespace Arm64

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

/-! ## Reaching a final state -/

/-! ## Code loaded, fetch -/

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

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

end exec

/-! ## Flags of `cmp` -/

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

end Poly1305DebianCtFw

end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw

open Arm64 Arm64.Obj

/-! ## Decoding by masks -/

theorem beq_false_of_mask {w K A M C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A &&& M) :
    (w &&& M == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, ← hK, BitVec.and_assoc, BitVec.and_comm M K, ← BitVec.and_assoc]

theorem beq_false_of_mask' {w K A C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A) :
    (w == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, hK]

/-! ## `ADRP xN` and `LDR xN, [xN, :lo12:]` words -/

end Poly1305DebianCtApi

end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw

open Arm64 Arm64.Obj

section
variable {pl : Placement} {ex : String → Option (State → State)} {m : Memory} (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl)

end

end Poly1305DebianCtApi

end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw

open Arm64 Arm64.Obj

end Poly1305DebianCtApi

end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw

open Arm64 Arm64.Obj

/-! ## Reading the pointer and the table -/

/-! ## The specs look at the entry state only through `sp` and `x0`–`x3` -/


/-! ## The code of the entry points -/

section
variable {pl : Placement} {ex : String → Option (State → State)}
  (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl)
include hP

end

end Poly1305DebianCtApi

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

/-! ## The observation of one step -/

/-! ## Stop conditions -/

/-! ## Observational equivalence, backwards -/

section rules
variable {p : Program} {ar : String → Nat} {stop₁ stop₂ : State → Prop}


end rules

/-! ## Observation sequences compose -/

/-! ## From a relational lemma to `ct_subroutine_ok` -/

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

end exec

/-! ## Two-cell frames -/

/-! ## Stepping, and calls -/

end Poly1305DebianCtFw

end
end

section
section
/-! # Two runs on `mkS` states, the dispatch wrapper, and permissions under stores

Both runs of a constant-time proof are written `mkS s₁ pc rⱼ sp psⱼ mⱼ vⱼ` over the first run's
entry state `s₁` (the entries differ only in memory, `Poly1305DebianCtFw.sameExceptMem_eq`), so
`pc`, `sp` and the status agree by construction. `oe_mk` is the framework's `oe_exec` on such
pairs, threading `CodeLoaded`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw

open Arm64 Arm64.Obj Leakage

/-! ## Memory permissions survive stores -/

/-! ## Instruction shapes not in the framework -/

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

end exec

/-! ## The step rule on `mkS` pairs -/

section rules
variable {p : Program} {ar : String → Nat} {stop₁ stop₂ : State → Prop}

end rules

end Poly1305DebianCtApi

end
end

section
section
/-! # `crypto_onetimeauth_init` is constant-time

`crypto_onetimeauth_init` (text 0x48): `bti c; b crypto_onetimeauth_poly1305_init`; that (0xe0):
`bti c; adrp x2, implementation; ldr x2, [x2, :lo12:implementation]; ldr x2, [x2, #16];
mov x16, x2; br x16`, reaching the donna `_init` (0x3ac = 940) through the table entry, which both
runs read from the library's data in its initial state. The donna `_init` is straight-line:

`bti c; ldp x2, x3, [x1]; stp xzr, xzr, [x0, #0x18]; str xzr, [x0, #0x28];
and x4, x2, #0xfffffffffff; extr x2, x3, x2, #44; and x2, x2, #0xfffffffffff;
and x4, x4, #0xfffffffc0fffffff; and x2, x2, #0xffffffffffc0ffff; stp x4, x2, [x0];
mov x2, #0xfffff0000; movk x2, #0xfc0f; and x3, x2, x3, lsr #24; str x3, [x0, #0x10];
ldr x2, [x1, #0x10]; str x2, [x0, #0x30]; ldr x1, [x1, #0x18]; stp x1, xzr, [x0, #0x38];
strb wzr, [x0, #0x58]; mov w0, #0; ret`.

Every address it touches is `x0` or `x1` plus a constant, so both runs reveal the same addresses;
the key words land in `x1`–`x4` (different in the two runs) and are only stored. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw

open Arm64 Arm64.Obj Leakage
open Poly1305DebianCt (lib arity initPre initPub preSpec ctPublicOk)
open Poly1305Libsodium (bytesIn)

/-! ## Permissions from the precondition -/

/-! ## The run -/

section run
variable {pl : Placement} {ex : String → Option (State → State)} (hP : lib.Placeable pl) {m : Memory}

end run

end Poly1305DebianCtApi

end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Arm64 Arm64.Obj

/-! ## Decoding by masks -/

theorem gd_decode_adr_class (w : BitVec 32) (hK : w &&& 0x1f000000#32 = 0x10000000#32) :
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

theorem gd_decode_addimm_class (w : BitVec 32) (hK : w &&& 0x1f800000#32 = 0x11000000#32) :
    decode w = some (
      let op := AddSubOp.ofBits (w.getLsbD 30) (w.getLsbD 29)
      .addSubImm (RegWidth.ofBool (w.getLsbD 31)) op
        (if op.setsFlags then Reg.fromZRBits (w.extractLsb' 0 5) else Reg.fromSPBits (w.extractLsb' 0 5))
        (Reg.fromSPBits (w.extractLsb' 5 5)) (w.extractLsb' 10 12) (w.getLsbD 22)) := by
  rw [decode]
  simp only [beq_false_of_mask' hK (C := 0xd503201f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4000001#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4200000#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd503201f#32) (M := 0xfffff01f#32) (by decide),
    beq_false_of_mask hK (C := 0#32) (M := 0xffff0000#32) (by decide),
    beq_false_of_mask hK (C := 0xd50b7420#32) (M := 0xffffffe0#32) (by decide),
    beq_false_of_mask hK (C := 0x10000000#32) (M := 0x1f000000#32) (by decide), hK]
  simp

/-- The two `ldr xN, [xN]` words (`N = 4, 0`). -/
def GLdr (A : BitVec 32) (n : BitVec 5) : Prop :=
  (A = 0xf9400084#32 ∧ n = 4#5) ∨ (A = 0xf9400000#32 ∧ n = 0#5)

/-- The two `adrp xN` words (`N = 4, 0`) with their immediate cleared. -/
def GAdrp (W : BitVec 32) (n : BitVec 5) : Prop :=
  (W = 0x90000004#32 ∧ n = 4#5) ∨ (W = 0x90000000#32 ∧ n = 0#5)

theorem gd_decode_ldr (w A : BitVec 32) (n : BitVec 5) (hA : GLdr A n)
    (hK : w &&& 0xffc003ff#32 = A) :
    decode w = some (.ldr .W64 .X64 false (.gpr n)
      (.Offset (.gpr n) (((w.extractLsb' 10 12).zeroExtend 64) <<< 3))) := by
  rcases hA with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ <;>
  · rw [decode]
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
    have e30 : BitVec.extractLsb' 30 2 w = 3#2 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := hb (30 + i)
      simp only [BitVec.getLsbD_extractLsb'] at this ⊢
      interval_cases i <;> simp_all
    have e22 : BitVec.extractLsb' 22 2 w = 1#2 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := hb (22 + i)
      simp only [BitVec.getLsbD_extractLsb'] at this ⊢
      interval_cases i <;> simp_all
    have e0 : BitVec.extractLsb' 0 5 w = n := by
      subst hn
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := hb (0 + i)
      simp only [BitVec.getLsbD_extractLsb'] at this ⊢
      interval_cases i <;> simp_all
    have e5 : BitVec.extractLsb' 5 5 w = n := by
      subst hn
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := hb (5 + i)
      simp only [BitVec.getLsbD_extractLsb'] at this ⊢
      interval_cases i <;> simp_all
    rw [if_pos hc, e30, e22, e0, e5]
    subst hn
    rfl

/-! ## Page arithmetic -/

theorem gd_hi_bits32 (D : BitVec 64) (h1 : -(2^32:Int) ≤ D.toInt) (h2 : D.toInt < 2^32) :
    ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  interval_cases i <;> (try simp only [decide_eq_decide]) <;> (try split at h1) <;> omega

theorem gd_hi_bits20 (D : BitVec 64) (h1 : -(2^20:Int) ≤ D.toInt) (h2 : D.toInt < 2^20) :
    ∀ i, 20 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 20 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  interval_cases i <;> (try simp only [decide_eq_decide]) <;> (try split at h1) <;> omega

theorem gd_pageOf_eq (x : BitVec 64) : pageOf x = (x >>> 12) <<< 12 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [pageOf, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem gd_pageOf_toNat (x : BitVec 64) : (pageOf x).toNat = x.toNat / 4096 * 4096 := by
  rw [gd_pageOf_eq]; simp [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]; omega

theorem gd_lo_bits (a b : BitVec 64) : ∀ i, i < 12 → (pageOf a - pageOf b).getLsbD i = false := by
  intro i hi
  have h : (pageOf a - pageOf b).toNat % 4096 = 0 := by
    rw [BitVec.toNat_sub, gd_pageOf_toNat, gd_pageOf_toNat]
    have := a.isLt; have := b.isLt; omega
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  generalize (pageOf a - pageOf b).toNat = n at h ⊢
  interval_cases i <;> simp <;> omega

/-! ## `ADRP xN` -/

theorem gd_adrpW_mask {W : BitVec 32} {n : BitVec 5} (hW : GAdrp W n) (D : BitVec 64) :
    adrpWordOff W D &&& 0x1f000000#32 = 0x10000000#32 := by
  rcases hW with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [adrpWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem gd_adrpW_31 {W : BitVec 32} {n : BitVec 5} (hW : GAdrp W n) (D : BitVec 64) :
    (adrpWordOff W D).getLsbD 31 = true := by
  rcases hW with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [adrpWordOff]

theorem gd_adrpW_rd {W : BitVec 32} {n : BitVec 5} (hW : GAdrp W n) (D : BitVec 64) :
    (adrpWordOff W D).extractLsb' 0 5 = n := by
  rcases hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [adrpWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem gd_adrpW_off {W : BitVec 32} {n : BitVec 5} (hW : GAdrp W n) (D : BitVec 64)
    (hlo : ∀ i, i < 12 → D.getLsbD i = false)
    (hhi : ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32) :
    ((adrpWordOff W D).extractLsb' 5 19 ++ (adrpWordOff W D).extractLsb' 29 2).signExtend 64 <<< 12
      = D := by
  rcases hW with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [adrpWordOff, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend,
      BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getMsbD]
    interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
      first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
        exact (hhi _ (by omega) (by omega)).symm

theorem gd_decode_adrp {W : BitVec 32} {n : BitVec 5} (hW : GAdrp W n) {P T : BitVec 64}
    (hr : AdrpInRange P T) :
    decode (adrpWord W P T) = some (.adr true (.gpr n) (pageOf T - pageOf P)) := by
  rw [adrpWord, gd_decode_adr_class _ (gd_adrpW_mask hW _), gd_adrpW_31 hW, gd_adrpW_rd hW,
    gd_adrpW_off hW _ (gd_lo_bits T P) (gd_hi_bits32 _ hr.1 hr.2)]
  rcases hW with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl

/-! ## `LDR xN, [xN, :lo12:]` -/

theorem gd_lo12W_mask {A : BitVec 32} {n : BitVec 5} (hA : GLdr A n) (T : BitVec 64) :
    lo12Word 3 A T &&& 0xffc003ff#32 = A := by
  rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [lo12Word, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem gd_lo12_imm (A : BitVec 32) (T : BitVec 64) (hal : T &&& 7#64 = 0#64) :
    ((lo12Word 3 A T).extractLsb' 10 12).zeroExtend 64 <<< 3 = T &&& 0xfff#64 := by
  have hb : ∀ i, i < 3 → T.getLsbD i = false := by
    intro i hi
    have := congrArg (fun x => x.getLsbD i) hal
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
    interval_cases i <;> simp_all
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;> exact hb _ (by omega)

theorem gd_decode_ldr_lo12 {A : BitVec 32} {n : BitVec 5} (hA : GLdr A n) (T : BitVec 64)
    (hal : Lo12Aligned 3 T) :
    decode (lo12Word 3 A T) =
      some (.ldr .W64 .X64 false (.gpr n) (.Offset (.gpr n) (T &&& 0xfff#64))) := by
  rw [gd_decode_ldr _ A n hA (gd_lo12W_mask hA T), gd_lo12_imm A T hal]

/-! ## `ADD xN, xN, :lo12:` (the relaxed `LDR`) -/

theorem gd_ldrToAdd {A : BitVec 32} {n : BitVec 5} (hA : GLdr A n) :
    (ldrToAddWord A = 0x91000084#32 ∧ n = 4#5) ∨ (ldrToAddWord A = 0x91000000#32 ∧ n = 0#5) := by
  rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨by decide, rfl⟩
  · exact Or.inr ⟨by decide, rfl⟩

theorem gd_decode_add {A : BitVec 32} {n : BitVec 5} (hA : GLdr A n) (T : BitVec 64) :
    decode (lo12Word 0 (ldrToAddWord A) T) =
      some (.addSubImm .W64 .ADD (.gpr n) (.gpr n) (T.extractLsb' 0 12) false) := by
  rcases gd_ldrToAdd hA with ⟨hB, rfl⟩ | ⟨hB, rfl⟩ <;> rw [hB]
  all_goals
    have hm : lo12Word 0 (ldrToAddWord A) T &&& 0x1f800000#32 = 0x11000000#32 := by
      rw [hB]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [lo12Word, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
      interval_cases i <;> simp
    rw [hB] at hm
    rw [gd_decode_addimm_class _ hm]
    have b31 : (lo12Word 0 (ldrToAddWord A) T).getLsbD 31 = true := by rw [hB]; simp [lo12Word]
    have b30 : (lo12Word 0 (ldrToAddWord A) T).getLsbD 30 = false := by rw [hB]; simp [lo12Word]
    have b29 : (lo12Word 0 (ldrToAddWord A) T).getLsbD 29 = false := by rw [hB]; simp [lo12Word]
    have b22 : (lo12Word 0 (ldrToAddWord A) T).getLsbD 22 = false := by rw [hB]; simp [lo12Word]
    rw [hB] at b31 b30 b29 b22
    rw [b31, b30, b29, b22]
    have imm : (lo12Word 0 (ldrToAddWord A) T).extractLsb' 10 12 = T.extractLsb' 0 12 := by
      rw [hB]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
        BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
      interval_cases i <;> simp
    rw [hB] at imm
    rw [imm]
  · have r0 : (lo12Word 0 0x91000084#32 T).extractLsb' 0 5 = 4#5 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
        BitVec.getLsbD_shiftLeft]
      interval_cases i <;> simp
    have r5 : (lo12Word 0 0x91000084#32 T).extractLsb' 5 5 = 4#5 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
        BitVec.getLsbD_shiftLeft]
      interval_cases i <;> simp
    rw [r0, r5]; rfl
  · have r0 : (lo12Word 0 0x91000000#32 T).extractLsb' 0 5 = 0#5 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
        BitVec.getLsbD_shiftLeft]
      interval_cases i <;> simp
    have r5 : (lo12Word 0 0x91000000#32 T).extractLsb' 5 5 = 0#5 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
        BitVec.getLsbD_shiftLeft]
      interval_cases i <;> simp
    rw [r0, r5]; rfl

/-! ## `ADR xN` (the relaxed `LDR` after a `NOP`) -/

theorem gd_adrTmpl {A : BitVec 32} {n : BitVec 5} (hA : GLdr A n) :
    (adrTemplate A = 0x10000004#32 ∧ n = 4#5) ∨ (adrTemplate A = 0x10000000#32 ∧ n = 0#5) := by
  rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨by decide, rfl⟩
  · exact Or.inr ⟨by decide, rfl⟩

theorem gd_decode_adr {A : BitVec 32} {n : BitVec 5} (hA : GLdr A n) {P T : BitVec 64}
    (hr : AdrInRange P T) :
    decode (adrWord (adrTemplate A) P T) = some (.adr false (.gpr n) (T - P)) := by
  have hhi := gd_hi_bits20 _ hr.1 hr.2
  rw [adrWord]
  generalize T - P = D at hhi
  rcases gd_adrTmpl hA with ⟨hB, rfl⟩ | ⟨hB, rfl⟩ <;> rw [hB]
  all_goals
    have hm : adrWordOff (adrTemplate A) D &&& 0x1f000000#32 = 0x10000000#32 := by
      rw [hB]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [adrWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
      interval_cases i <;> simp
    rw [hB] at hm
    rw [gd_decode_adr_class _ hm]
    have b31 : (adrWordOff (adrTemplate A) D).getLsbD 31 = false := by rw [hB]; simp [adrWordOff]
    rw [hB] at b31
    rw [b31, if_neg (by decide)]
    have hoff : ((adrWordOff (adrTemplate A) D).extractLsb' 5 19 ++
        (adrWordOff (adrTemplate A) D).extractLsb' 29 2).signExtend 64 = D := by
      rw [hB]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [adrWordOff, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
        BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getLsbD_shiftLeft]
      interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
        first | rfl | exact hhi _ (by omega) (by omega) |
          exact (hhi _ (by omega) (by omega)).symm
    rw [hB] at hoff
    rw [hoff]
  · have r0 : (adrWordOff 0x10000004#32 D).extractLsb' 0 5 = 4#5 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [adrWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
        BitVec.getLsbD_shiftLeft]
      interval_cases i <;> simp
    rw [r0]; rfl
  · have r0 : (adrWordOff 0x10000000#32 D).extractLsb' 0 5 = 0#5 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [adrWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
        BitVec.getLsbD_shiftLeft]
      interval_cases i <;> simp
    rw [r0]; rfl

theorem gd_decode_nop : decode nopWord = some .nop := by decide

end Poly1305DebianCtApi

end
end

section
section
set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw
open Poly1305DebianCt (lib MemsetOk GuardUniform guardSites guardDirect)

open Arm64 Arm64.Obj

abbrev gSym : String := "__stack_chk_guard"

theorem gd_lookup : lookup gSym Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.symbols = none := by decide

theorem gd_target (pl : Placement) (o : Nat) (k : RelocKind) :
    Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.target pl { off := o, kind := k, sym := gSym } = pl.ρ gSym := by
  simp [CodeBlock.target, CodeBlock.resolve, gd_lookup, addSignedAddr]

theorem gd_relocTarget (pl : Placement) (o : Nat) (k : RelocKind)
    (hk : (k == .call26 || k == .jump26) = false) :
    Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocTarget pl o { off := o, kind := k, sym := gSym } =
      pl.ρ gSym := by
  have hb : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.b2bNext? { off := o, kind := k, sym := gSym } = none := by
    simp [CodeBlock.b2bNext?, hk]
  simp only [CodeBlock.relocTarget, hb, ite_self, gd_target]

/-! ## The relocated words -/

section words
variable (pl : Placement)

theorem gd_pw1420 :
    Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl 1420 =
      if pl.relax 1420 then nopWord
      else adrpWord 0x90000004#32 (pl.base + BitVec.ofNat 64 1420) (pl.ρ gSym) := by
  have hr : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocAt? 1420 =
      some { off := 1420, kind := .adrGotPage, sym := gSym } := by decide
  have hw : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.wordAt 1420 = 0x90000004#32 := by decide +kernel
  have h1 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxableAt 1420 = false := by decide +kernel
  have h2 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxableAt 1416 = false := by decide +kernel
  have g0 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.gotPairAt 1416 = false := by decide +kernel
  have g1 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.gotPairAt 1420 = true := by decide +kernel
  have ht := gd_relocTarget pl 1420 .adrGotPage rfl
  cases h : pl.relax 1420 <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, hr, hw, h1, h2, g0, g1, ht,
      CodeBlock.undefWeakBranch, patchRelocWord, RelocKind.isGotOrTlsIe,
      CodeBlock.patchGotOrTlsIeRelaxed]

theorem gd_pw1424 :
    Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl (1420 + 4) =
      if pl.relax 1420 then
        adrWord (adrTemplate 0xf9400084#32) (pl.base + BitVec.ofNat 64 (1420 + 4)) (pl.ρ gSym)
      else if pl.relax (1420 + 4) then lo12Word 0 (ldrToAddWord 0xf9400084#32) (pl.ρ gSym)
      else lo12Word 3 0xf9400084#32 (pl.ρ gSym) := by
  have hr : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocAt? 1424 =
      some { off := 1424, kind := .ld64GotLo12Nc, sym := gSym } := by decide
  have hw : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.wordAt 1424 = 0xf9400084#32 := by decide +kernel
  have h1 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxableAt 1420 = false := by decide +kernel
  have h2 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxableAt 1424 = false := by decide +kernel
  have g1 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.gotPairAt 1420 = true := by decide +kernel
  have ht := gd_relocTarget pl 1424 .ld64GotLo12Nc rfl
  cases h : pl.relax 1420 <;> cases h' : pl.relax 1424 <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h', hr, hw, h1, h2, g1, ht,
      CodeBlock.undefWeakBranch, gd_target, patchRelocWord, RelocKind.isGotOrTlsIe,
      CodeBlock.patchGotOrTlsIeRelaxed]

theorem gd_pw1544 :
    Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl 1544 =
      if pl.relax 1544 then nopWord
      else adrpWord 0x90000000#32 (pl.base + BitVec.ofNat 64 1544) (pl.ρ gSym) := by
  have hr : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocAt? 1544 =
      some { off := 1544, kind := .adrGotPage, sym := gSym } := by decide
  have hw : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.wordAt 1544 = 0x90000000#32 := by decide +kernel
  have h1 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxableAt 1544 = false := by decide +kernel
  have h2 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxableAt 1540 = false := by decide +kernel
  have g0 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.gotPairAt 1540 = false := by decide +kernel
  have g1 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.gotPairAt 1544 = true := by decide +kernel
  have ht := gd_relocTarget pl 1544 .adrGotPage rfl
  cases h : pl.relax 1544 <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, hr, hw, h1, h2, g0, g1, ht,
      CodeBlock.undefWeakBranch, patchRelocWord, RelocKind.isGotOrTlsIe,
      CodeBlock.patchGotOrTlsIeRelaxed]

theorem gd_pw1548 :
    Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl (1544 + 4) =
      if pl.relax 1544 then
        adrWord (adrTemplate 0xf9400000#32) (pl.base + BitVec.ofNat 64 (1544 + 4)) (pl.ρ gSym)
      else if pl.relax (1544 + 4) then lo12Word 0 (ldrToAddWord 0xf9400000#32) (pl.ρ gSym)
      else lo12Word 3 0xf9400000#32 (pl.ρ gSym) := by
  have hr : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocAt? 1548 =
      some { off := 1548, kind := .ld64GotLo12Nc, sym := gSym } := by decide
  have hw : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.wordAt 1548 = 0xf9400000#32 := by decide +kernel
  have h1 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxableAt 1544 = false := by decide +kernel
  have h2 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relaxableAt 1548 = false := by decide +kernel
  have g1 : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.gotPairAt 1544 = true := by decide +kernel
  have ht := gd_relocTarget pl 1548 .ld64GotLo12Nc rfl
  cases h : pl.relax 1544 <;> cases h' : pl.relax 1548 <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h', hr, hw, h1, h2, g1, ht,
      CodeBlock.undefWeakBranch, gd_target, patchRelocWord, RelocKind.isGotOrTlsIe,
      CodeBlock.patchGotOrTlsIeRelaxed]

end words

/-! ## Range facts -/

section ranges
variable {pl : Placement} (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl)
include hP

theorem gd_range_adrp (o : Nat) (ho : o = 1420 ∨ o = 1544) (hrel : pl.relax o = false) :
    AdrpInRange (pl.base + BitVec.ofNat 64 o) (pl.ρ gSym) := by
  have hmem : ({ off := o, kind := .adrGotPage, sym := gSym } : RelocEntry) ∈
      Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocs := by
    rcases ho with rfl | rfl <;> decide
  have hPt : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.Placeable pl := hP.text
  have h := (hPt.relocs_ok _ hmem).2.2
  rw [gd_relocTarget pl o .adrGotPage rfl] at h
  simpa [CodeBlock.relocInRange, hrel] using h

theorem gd_range_adr (o : Nat) (ho : o = 1420 ∨ o = 1544) (hrel : pl.relax o = true) :
    AdrInRange (pl.base + BitVec.ofNat 64 (o + 4)) (pl.ρ gSym) := by
  have hmem : ({ off := o + 4, kind := .ld64GotLo12Nc, sym := gSym } : RelocEntry) ∈
      Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocs := by
    rcases ho with rfl | rfl <;> decide
  have hg : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.gotPairAt o = true := by
    rcases ho with rfl | rfl <;> decide +kernel
  have hPt : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.Placeable pl := hP.text
  have h := (hPt.relocs_ok _ hmem).2.2
  rw [gd_relocTarget pl (o + 4) .ld64GotLo12Nc rfl] at h
  simpa [CodeBlock.relocInRange, hrel, hg] using h

theorem gd_range_lo12 (o : Nat) (ho : o = 1420 ∨ o = 1544) (h1 : pl.relax o = false)
    (h2 : pl.relax (o + 4) = false) : Lo12Aligned 3 (pl.ρ gSym) := by
  have hmem : ({ off := o + 4, kind := .ld64GotLo12Nc, sym := gSym } : RelocEntry) ∈
      Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.relocs := by
    rcases ho with rfl | rfl <;> decide
  have hPt : Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.Placeable pl := hP.text
  have h := (hPt.relocs_ok _ hmem).2.2
  rw [gd_relocTarget pl (o + 4) .ld64GotLo12Nc rfl] at h
  simpa [CodeBlock.relocInRange, h1, h2] using h

end ranges

/-! ## Steps -/

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
  {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}

end exec


/-! ## Reading the 8 read-only bytes of a word (bytesIn_byte, bytesIn_read64 from the same proof's MemX) -/

end Poly1305DebianCtApi

end
end

section
section
/-! # The one-shot's two stack-guard GOT sites decode as stated (`gd_site` of the accepted
functional proof, without the fetch) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305DebianCtApi
open Poly1305DebianCtFw
open Arm64 Arm64.Obj

theorem oneshot_guard_reloc_decode_dev (pl : Placement)
    (hP : Poly1305DebianCt.libsodiumDebianOnetimeauthCtLib.Placeable pl) :
      ∀ (off : Nat) (n : BitVec 5), (off = 1420 ∧ n = 4#5) ∨ (off = 1544 ∧ n = 0#5) →
        (pl.relax off = true →
          decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl off) = some .nop ∧
          decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl (off + 4)) =
            some (.adr false (.gpr n)
              (pl.ρ "__stack_chk_guard" - (pl.base + BitVec.ofNat 64 (off + 4))))) ∧
        (pl.relax off = false →
          decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl off) =
            some (.adr true (.gpr n)
              (pageOf (pl.ρ "__stack_chk_guard") - pageOf (pl.base + BitVec.ofNat 64 off)))) ∧
        (pl.relax off = false → pl.relax (off + 4) = true →
          decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl (off + 4)) =
            some (.addSubImm .W64 .ADD (.gpr n) (.gpr n)
              ((pl.ρ "__stack_chk_guard").extractLsb' 0 12) false)) ∧
        (pl.relax off = false → pl.relax (off + 4) = false →
          decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl (off + 4)) =
            some (.ldr .W64 .X64 false (.gpr n)
              (.Offset (.gpr n) (pl.ρ "__stack_chk_guard" &&& 0xfff#64)))) := by
  intro off n hs
  have ho : off = 1420 ∨ off = 1544 := by rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  obtain ⟨W, A, hW, hA, pw1, pw2⟩ : ∃ W A : BitVec 32, GAdrp W n ∧ GLdr A n ∧
      Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl off =
        (if pl.relax off then nopWord
         else adrpWord W (pl.base + BitVec.ofNat 64 off) (pl.ρ gSym)) ∧
      Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl (off + 4) =
        (if pl.relax off then
          adrWord (adrTemplate A) (pl.base + BitVec.ofNat 64 (off + 4)) (pl.ρ gSym)
        else if pl.relax (off + 4) then lo12Word 0 (ldrToAddWord A) (pl.ρ gSym)
        else lo12Word 3 A (pl.ρ gSym)) := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, _, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, gd_pw1420 pl, gd_pw1424 pl⟩
    · exact ⟨_, _, Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, gd_pw1544 pl, gd_pw1548 pl⟩
  have hf1 : decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl off) =
      decode (if pl.relax off then nopWord
         else adrpWord W (pl.base + BitVec.ofNat 64 off) (pl.ρ gSym)) := by rw [pw1]
  have hf2 : decode (Poly1305DebianCt.libsodiumDebianOnetimeauthCtText.patchedWord pl (off + 4)) =
      decode (if pl.relax off then
          adrWord (adrTemplate A) (pl.base + BitVec.ofNat 64 (off + 4)) (pl.ρ gSym)
        else if pl.relax (off + 4) then lo12Word 0 (ldrToAddWord A) (pl.ρ gSym)
        else lo12Word 3 A (pl.ρ gSym)) := by rw [pw2]
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · simp only [h1, if_true] at hf1 hf2
    rw [gd_decode_nop] at hf1
    rw [gd_decode_adr hA (gd_range_adr hP off ho h1)] at hf2
    exact ⟨hf1, hf2⟩
  · simp only [h1, Bool.false_eq_true, if_false] at hf1
    rw [hf1, gd_decode_adrp hW (gd_range_adrp hP off ho h1)]
  · simp only [h1, h2, Bool.false_eq_true, if_false, if_true] at hf2
    rw [hf2, gd_decode_add hA]
  · simp only [h1, h2, Bool.false_eq_true, if_false] at hf2
    rw [hf2, gd_decode_ldr_lo12 hA _ (gd_range_lo12 hP off ho h1 h2)]

end Poly1305DebianCtApi

end
end

section
open Poly1305DebianCt

open Arm64 Arm64.Obj


theorem solution (pl : Placement)
    (hP : libsodiumDebianOnetimeauthCtLib.Placeable pl) :
      ∀ (off : Nat) (n : BitVec 5), (off = 1420 ∧ n = 4#5) ∨ (off = 1544 ∧ n = 0#5) →
        (pl.relax off = true →
          decode (libsodiumDebianOnetimeauthCtText.patchedWord pl off) = some .nop ∧
          decode (libsodiumDebianOnetimeauthCtText.patchedWord pl (off + 4)) =
            some (.adr false (.gpr n)
              (pl.ρ "__stack_chk_guard" - (pl.base + BitVec.ofNat 64 (off + 4))))) ∧
        (pl.relax off = false →
          decode (libsodiumDebianOnetimeauthCtText.patchedWord pl off) =
            some (.adr true (.gpr n)
              (pageOf (pl.ρ "__stack_chk_guard") - pageOf (pl.base + BitVec.ofNat 64 off)))) ∧
        (pl.relax off = false → pl.relax (off + 4) = true →
          decode (libsodiumDebianOnetimeauthCtText.patchedWord pl (off + 4)) =
            some (.addSubImm .W64 .ADD (.gpr n) (.gpr n)
              ((pl.ρ "__stack_chk_guard").extractLsb' 0 12) false)) ∧
        (pl.relax off = false → pl.relax (off + 4) = false →
          decode (libsodiumDebianOnetimeauthCtText.patchedWord pl (off + 4)) =
            some (.ldr .W64 .X64 false (.gpr n)
              (.Offset (.gpr n) (pl.ρ "__stack_chk_guard" &&& 0xfff#64)))) := by
  apply Poly1305DebianCtApi.oneshot_guard_reloc_decode_dev <;> assumption

end
