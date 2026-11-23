-- Prove2me | solution 1 for X25519Dalek.basepointTable_mul_base_prologue
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T20:26:08.562775+00:00
-- url     : https://prove2.me/submissions/cbdf4cb6-1d23-4181-badb-9cb7b5fa5d71

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_X25519Dalek_Spec
import Theorems.Thm_X25519Dalek_steps_keepsFrozen_v2
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_X25519Dalek_fnOk_scalar_as_radix_16_v2
set_option linter.all false

section
/-! # Separation-logic heap algebra

Ported from google-deepmind/code-verification @ 8c8d371f (Apache-2.0),
`arm64-semantics/ProofLib/CoreLemmas.lean` and `ProofLib/SepLogic/Model.lean`: the plain lemmas
about `Heap.Disjoint`, `Heap.union`, `Heap.Matches` and `sepConj`, with ProofLib's custom simp
attributes removed. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

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

/-- Left commutativity of separating conjunction: `P ∗ (Q ∗ R) = Q ∗ (P ∗ R)`. -/
theorem sepConj_left_comm (P Q R : SepProp) : (P ∗ (Q ∗ R)) = (Q ∗ (P ∗ R)) := by
  rw [← sepConj_assoc, sepConj_comm P Q, sepConj_assoc]

instance instAssociativeSepConj : Std.Associative SepProp.sepConj where
  assoc := sepConj_assoc

instance instCommutativeSepConj : Std.Commutative SepProp.sepConj where
  comm := sepConj_comm

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

namespace Memory

theorem KeepsFrozen.refl (m : Memory) : m.KeepsFrozen m := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

theorem KeepsFrozen.trans {m₁ m₂ m₃ : Memory} (h₁ : m₁.KeepsFrozen m₂) (h₂ : m₂.KeepsFrozen m₃) :
    m₁.KeepsFrozen m₃ := by
  intro a ha
  obtain ⟨hb₁, hp₁, hlf₁, ha₁⟩ := h₁ a ha
  have ha₂ : m₂.Frozen a := by unfold Frozen at *; rw [hp₁]; exact ha
  obtain ⟨hb₂, hp₂, hlf₂, ha₂'⟩ := h₂ a ha₂
  exact ⟨hb₂.trans hb₁, hp₂.trans hp₁, hlf₂.trans hlf₁, ha₂'.trans ha₁⟩

theorem keepsFrozen_write8 {m : Memory} {x : BitVec 64} (h : m.canWrite x 1 = true) (v : BitVec 8) :
    m.KeepsFrozen (m.write8 x v) := by
  intro a ha
  have hw : (m.perm x).w = true := by
    simp only [canWrite, allPerm, Bool.and_true, Bool.and_eq_true] at h; exact h.1
  have hne : a ≠ x := by
    intro e; subst e
    unfold Frozen at ha
    cases hp : m.perm a with
    | none => rw [hp] at hw; simp at hw
    | some p =>
      rw [hp] at hw ha; simp [Option.frozen, Perm.frozen] at hw ha; simp_all
  exact ⟨read8_write8_ne' _ _ hne, perm_write8' _ _ _ _, isLazyFree_write8_ne' _ _ hne, isAnon_write8' _ _ _ _⟩

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

section
/-! # 64-bit cells and byte reads: values and permissions from ownership -/

set_option autoImplicit false

namespace Arm64

theorem dand {P : Prop} [Decidable P] (h : P) (a : Bool) : (decide P && a) = a := by simp [h]

theorem concat8_extract (v : BitVec 64) :
    v.extractLsb' 56 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 40 8 ++ v.extractLsb' 32 8 ++
      v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> simp <;> first | (intro; omega) | (rw [dand] <;> first | omega | (congr 1; omega))

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

theorem keepsFrozen_write8_of_rw {m : Memory} {x : BitVec 64} (h : m.perm x = some Perm.rw) (v : BitVec 8) :
    m.KeepsFrozen (m.write8 x v) :=
  Memory.keepsFrozen_write8 (canWrite_of (n := 1) (fun i hi => by
    have : i = 0 := by omega
    subst this; simpa using h)) v

theorem keepsFrozen_write64_of_rw {m : Memory} {a : BitVec 64}
    (h : ∀ i < 8, m.perm (a + BitVec.ofNat 64 i) = some Perm.rw) (w : BitVec 64) :
    m.KeepsFrozen (m.write64 a w) := by
  have p : ∀ (m' : Memory) (i : Nat), i < 8 → (∀ y, m'.perm y = m.perm y) →
      m'.perm (a + BitVec.ofNat 64 i) = some Perm.rw := fun m' i hi hm => (hm _).trans (h i hi)
  have pw : ∀ (m' : Memory) (x : BitVec 64) (v : BitVec 8), (∀ y, m'.perm y = m.perm y) →
      ∀ y, (m'.write8 x v).perm y = m.perm y := fun m' x v hm y => (Memory.perm_write8' _ _ _ _).trans (hm y)
  simp only [Memory.write64]
  have st : ∀ (m' : Memory) (k : Nat), k < 8 → (∀ y, m'.perm y = m.perm y) → ∀ v : BitVec 8,
      m'.KeepsFrozen (m'.write8 (a + BitVec.ofNat 64 k) v) ∧
      ∀ y, (m'.write8 (a + BitVec.ofNat 64 k) v).perm y = m.perm y :=
    fun m' k hk hm v => ⟨keepsFrozen_write8_of_rw (p m' k hk hm) v, pw m' _ v hm⟩
  obtain ⟨k0, q0⟩ := st m 0 (by omega) (fun _ => rfl) (w.extractLsb' 0 8)
  obtain ⟨k1, q1⟩ := st _ 1 (by omega) q0 (w.extractLsb' 8 8)
  obtain ⟨k2, q2⟩ := st _ 2 (by omega) q1 (w.extractLsb' 16 8)
  obtain ⟨k3, q3⟩ := st _ 3 (by omega) q2 (w.extractLsb' 24 8)
  obtain ⟨k4, q4⟩ := st _ 4 (by omega) q3 (w.extractLsb' 32 8)
  obtain ⟨k5, q5⟩ := st _ 5 (by omega) q4 (w.extractLsb' 40 8)
  obtain ⟨k6, q6⟩ := st _ 6 (by omega) q5 (w.extractLsb' 48 8)
  obtain ⟨k7, _⟩ := st _ 7 (by omega) q6 (w.extractLsb' 56 8)
  exact k0.trans (k1.trans (k2.trans (k3.trans (k4.trans (k5.trans (k6.trans k7))))))

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

section
/-! # Instruction fetch in the placed x25519 library, and execution by backward chaining

`Step` does not depend on which block's program runs it when no hooks are installed, so a callee's
contract (stated for its own block) is usable from the caller's block. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

/-- Block `i` of the library. -/
def blk (i : Nat) : CodeBlock := x25519CliMultiLib.blocks.getD i { code := [] }

/-- Block `i`'s placed program, as in `fnOk`. -/
abbrev bprog (mpl : MultiPlacement) (i : Nat) : Program := x25519CliMultiLib.blockProgram mpl i

theorem hook_none (mpl : MultiPlacement) (i : Nat) (pc : BitVec 64) : (bprog mpl i).externAt? pc = none := by
  simp only [bprog, Program.externAt?, Program.hookAtOff?, MultiPlacedLib.blockProgram, PlacedLib.program]
  simp

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

theorem Steps.trans' {p : Program} {a b c : State} (h1 : Steps p a b) (h2 : Steps p b c) :
    Steps p a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact Steps.step h (ih h2)

theorem bsteps_transfer {mpl : MultiPlacement} {i j : Nat} {s s' : State}
    (h : Steps (bprog mpl i) s s') : Steps (bprog mpl j) s s' :=
  steps_transfer (hook_none mpl i) (hook_none mpl j) rfl h

/-! ## Reaching a final state -/

def Reach (p : Program) (s : State) (Q : State → Prop) : Prop := ∃ sf, Steps p s sf ∧ Q sf

theorem Reach.done {p : Program} {s : State} {Q : State → Prop} (h : Q s) : Reach p s Q :=
  ⟨s, Steps.refl s, h⟩

theorem Reach.exec {p : Program} {s : State} {Q : State → Prop} {i : Instr}
    (hrun : s.status = .Running) (hf : p.fetchMem s.mem s.pc = some i)
    (h : Reach p (execInstWithSvc (evalSvc p.svc) i s) Q) : Reach p s Q := by
  obtain ⟨sf, hst, hq⟩ := h
  exact ⟨sf, Steps.step (Step.exec hrun hf) hst, hq⟩

theorem Reach.steps {p : Program} {s s' : State} {Q : State → Prop} (h1 : Steps p s s')
    (h : Reach p s' Q) : Reach p s Q := by
  obtain ⟨sf, hst, hq⟩ := h
  exact ⟨sf, Steps.trans' h1 hst, hq⟩

/-! ## Fetching from the loaded code -/

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

theorem take4_drop_patched {b : CodeBlock} {pl : Placement} {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ b.code.length) :
    ((b.patched pl).drop off).take 4 = bytesOfWordLE (b.patchedWord pl off) := by
  have hj : off / 4 < (List.range (b.code.length / 4)).length := by
    simp only [List.length_range]; omega
  have h := drop_take_flatMap_bytesOfWordLE (fun j => b.patchedWord pl (4 * j))
    (List.range (b.code.length / 4)) (off / 4) hj
  rw [List.getElem_range, show 4 * (off / 4) = off by omega] at h
  exact h

theorem sum_replicate' (n k : Nat) : (List.replicate n k).sum = n * k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]

theorem patched_length (b : CodeBlock) (pl : Placement) (h4 : b.code.length % 4 = 0) :
    (b.patched pl).length = b.code.length := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE, List.map_const', List.length_range, sum_replicate']
  omega

theorem codeLoaded_cell {p : Program} {m : Memory} (h : p.CodeLoaded m) (i : Nat)
    (hi : i < p.code.length) :
    m.read8 (p.base + BitVec.ofNat 64 i) = p.code[i] ∧
    m.perm (p.base + BitVec.ofNat 64 i) = some Perm.rx := by
  unfold Program.CodeLoaded at h
  exact ⟨(h.2.2 i hi).1, (h.2.2 i hi).2.1⟩

theorem blocks_length : x25519CliMultiLib.blocks.length = 19 := rfl

theorem blk_placeable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {i : Nat}
    (hi : i < 19) : (blk i).Placeable (x25519CliMultiLib.blockPlacement mpl i) := by
  have := hP.blocks_ok i (by rw [blocks_length]; exact hi)
  simpa [blk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [blocks_length]; exact hi)]
    using this

theorem read8_code {mpl : MultiPlacement} {m : Memory} {i : Nat}
    (hCL : (bprog mpl i).CodeLoaded m) (h4 : (blk i).code.length % 4 = 0) {off k : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ (blk i).code.length) (hk : k < 4) :
    m.read8 (mpl.base i + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      ((blk i).patchedWord (x25519CliMultiLib.blockPlacement mpl i) off).extractLsb' (8 * k) 8 ∧
    m.perm (mpl.base i + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
  have hl : (bprog mpl i).code.length = (blk i).code.length := patched_length _ _ h4
  have h := codeLoaded_cell hCL (off + k) (by omega)
  have ha : mpl.base i + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
      (bprog mpl i).base + BitVec.ofNat 64 (off + k) := by
    show _ = mpl.base i + _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [ha]
  refine ⟨?_, h.2⟩
  rw [h.1]
  have ht := take4_drop_patched (b := blk i) (pl := x25519CliMultiLib.blockPlacement mpl i) hal hlen
  have hlp : ((blk i).patched (x25519CliMultiLib.blockPlacement mpl i)).length = (blk i).code.length :=
    patched_length _ _ h4
  have e1 : (bprog mpl i).code[off + k]'(by omega) =
      ((((blk i).patched (x25519CliMultiLib.blockPlacement mpl i)).drop off).take 4)[k]'(by
        simp only [List.length_take, List.length_drop, hlp]; omega) := by
    simp only [List.getElem_take, List.getElem_drop]; rfl
  rw [e1]
  simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * k + j < 32 := by omega
  simp [hj, this]; omega

theorem concat_bytes32 (w : BitVec 32) :
    (w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 0 8) = w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> simp <;> first | (intro; omega) | (rw [dand] <;> first | omega | (congr 1; omega))

/-- The instruction fetched at offset `off` of block `i`, by any hook-free program. -/
theorem fetch_word {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m : Memory}
    {i : Nat} (hi : i < 19) (hCL : (bprog mpl i).CodeLoaded m) {off : Nat} (hal : off % 4 = 0)
    (hlen : off + 4 ≤ (blk i).code.length) (p : Program) (hp : ∀ pc, p.externAt? pc = none) :
    p.fetchMem m (mpl.base i + BitVec.ofNat 64 off) =
      decode ((blk i).patchedWord (x25519CliMultiLib.blockPlacement mpl i) off) := by
  have hPl := blk_placeable hP hi
  have h4 : (blk i).code.length % 4 = 0 := hPl.len_aligned
  have hb4 : (mpl.base i).toNat % 4 = 0 := by
    have h1 := hPl.base_aligned; have h2 := hPl.align_pos
    simp only [MultiPlacedLib.blockPlacement] at h1
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h2.2) (Nat.dvd_of_mod_eq_zero h1))
  have hnw : (mpl.base i).toNat + (blk i).code.length ≤ 2 ^ 64 := hPl.no_wrap
  have hpc : (mpl.base i + BitVec.ofNat 64 off).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : off % 2 ^ 64 = off := Nat.mod_eq_of_lt (by omega)
    have h2 : ((mpl.base i).toNat + off) % 2 ^ 64 = (mpl.base i).toNat + off :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]; omega
  have r0 := read8_code hCL h4 hal hlen (k := 0) (by omega)
  have r1 := read8_code hCL h4 hal hlen (k := 1) (by omega)
  have r2 := read8_code hCL h4 hal hlen (k := 2) (by omega)
  have r3 := read8_code hCL h4 hal hlen (k := 3) (by omega)
  simp only [Program.fetchMem, hp, Option.isSome_none, Bool.false_eq_true, if_false, hpc,
    ne_eq, not_true_eq_false]
  generalize mpl.base i + BitVec.ofNat 64 off = a at *
  generalize (blk i).patchedWord (x25519CliMultiLib.blockPlacement mpl i) off = w at *
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at r0 r1 r2 r3
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at r0
  have hx : m.canExec a 4 = true := by
    simp only [Memory.canExec, Memory.allPerm, BitVec.add_assoc, BitVec.reduceAdd]
    simp [r0.2, r1.2, r2.2, r3.2, Perm.rx]
  simp only [hx, Bool.not_true, Bool.false_eq_true, if_false]
  congr 1
  simp only [Memory.read32, BitVec.add_zero]
  rw [r0.1, r1.1, r2.1, r3.1]
  exact concat_bytes32 w

theorem patchedWord_plain (b : CodeBlock) (pl : Placement) {off : Nat} (h : b.relocAt? off = none) :
    b.patchedWord pl off = b.wordAt off := by
  simp [CodeBlock.patchedWord, h]

end X25519Dalek.EMulB
end

section
/-! # Abstract machine states

Every state inside a block proof is `mkS s0 pc r sp ps m v`: the state `s0` with the program
counter, the general registers, the stack pointer, the flags, the memory and the vector registers
replaced. The instruction evaluators map such states to such states, and these lemmas let `simp`
compute the result without unfolding `State`. -/

set_option autoImplicit false

namespace X25519Dalek.EMulB

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

end X25519Dalek.EMulB
end

section
/-! # Code stays loaded; stepping on abstract states; small stack frames -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

theorem codeLoaded_keepsFrozen {p : Program} {m m' : Memory} (h : p.CodeLoaded m)
    (hk : m.KeepsFrozen m') : p.CodeLoaded m' := by
  unfold Program.CodeLoaded at h ⊢
  refine ⟨h.1, h.2.1, fun i hi => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.2.2 i hi
  have hf : m.Frozen (p.base + BitVec.ofNat 64 i) := by
    simp [Memory.Frozen, h2, Perm.rx, Perm.frozen, Perm.rwx]
  obtain ⟨k1, k2, k3, _⟩ := hk _ hf
  exact ⟨k1.trans h1, k2.trans h2, k3.trans h3⟩

theorem libCodeLoaded_keepsFrozen {mpl : MultiPlacement} {m m' : Memory}
    (h : x25519CliMultiLib.CodeLoaded mpl m) (hk : m.KeepsFrozen m') :
    x25519CliMultiLib.CodeLoaded mpl m' :=
  fun i hi => codeLoaded_keepsFrozen (h i hi) hk

/-- Fetch at offset `off` of block `i` from any memory that kept the frozen bytes of `m0`. -/
theorem fetch_at {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {i : Nat} (hi : i < 19) (j : Nat) {off : Nat}
    {inst : Instr}
    (h : (off % 4 = 0 ∧ off + 4 ≤ (blk i).code.length) ∧ (blk i).relocAt? off = none ∧
      decode ((blk i).wordAt off) = some inst)
    {m : Memory} (hk : m0.KeepsFrozen m) :
    (bprog mpl j).fetchMem m (mpl.base i + BitVec.ofNat 64 off) = some inst := by
  have hCL' := libCodeLoaded_keepsFrozen hCL hk i (by rw [blocks_length]; exact hi)
  rw [fetch_word hP hi hCL' h.1.1 h.1.2 _ (hook_none mpl j), patchedWord_plain _ _ h.2.1]
  exact h.2.2

theorem fetch_at' {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {i : Nat} (hi : i < 19) (j : Nat) {b : CodeBlock}
    (hb : blk i = b) {L : Nat} (hL : b.code.length = L) {off : Nat} {inst : Instr}
    (h4 : off % 4 = 0 ∧ off + 4 ≤ L)
    (hr : b.relocAt? off = none) (hd : decode (b.wordAt off) = some inst)
    {m : Memory} (hk : m0.KeepsFrozen m) :
    (bprog mpl j).fetchMem m (mpl.base i + BitVec.ofNat 64 off) = some inst :=
  fetch_at hP hCL hi j (by subst hb hL; exact ⟨h4, hr, hd⟩) hk

theorem Reach.mk {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {i : Instr} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some i)
    (h : Reach p (execInstWithSvc (evalSvc p.svc) i (mkS s0 pc r sp ps m v)) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q :=
  Reach.exec hrun hf h

theorem pc_add (b : BitVec 64) (k j : Nat) :
    b + BitVec.ofNat 64 k + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (k + j) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-! ## Byte lists of length 8 are words -/

def pack64 (l : List (BitVec 8)) : BitVec 64 :=
  l.getD 7 0 ++ l.getD 6 0 ++ l.getD 5 0 ++ l.getD 4 0 ++ l.getD 3 0 ++ l.getD 2 0 ++
    l.getD 1 0 ++ l.getD 0 0

theorem unpack64_cat8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    unpack64 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  simp only [unpack64, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    simp (disch := omega) only [hi, decide_eq_true, if_pos, if_neg, Nat.sub_sub, Nat.reduceAdd,
      Bool.true_and, Nat.add_sub_cancel_left, Nat.zero_add, decide_true, ite_true]
    try (congr 1; omega)

theorem unpack64_pack64 (l : List (BitVec 8)) (h : l.length = 8) : unpack64 (pack64 l) = l := by
  match l, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    simp only [pack64, List.getD_cons_zero, List.getD_cons_succ]
    exact unpack64_cat8 b0 b1 b2 b3 b4 b5 b6 b7

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

/-- Focus-free consequences of owning one 64-bit cell at the head. -/
theorem cell_write {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F)
    (w : BitVec 64) :
    m.canWrite a 8 = true ∧ m.KeepsFrozen (m.write64 a w) ∧ (m.write64 a w ⊨ (a ↦₆₄ w) ∗ F) := by
  have h := sat64_read hs
  exact ⟨h.2.2, keepsFrozen_write64_of_rw (fun i hi => (sat64_byte hs i hi).2.1) w, sat64_write hs w⟩

end X25519Dalek.EMulB
end

section
/-! # Arithmetic facts for the instruction evaluators and byte encodings -/

set_option autoImplicit false

namespace X25519Dalek.EMulB

open Arm64

@[simp] theorem awc_false_fst (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]
  omega

@[simp] theorem awc_true_fst (x y : BitVec 64) : (AddWithCarry64 x y true).1 = x + y + 1#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]
  omega

@[simp] theorem add_not_add_one (x y : BitVec 64) : x + ~~~y + 1#64 = x - y := by
  bv_omega

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem and15_toNat (x : BitVec 64) : (x &&& 15#64).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and]
  have : (15#64 : BitVec 64).toNat = 2 ^ 4 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem aligned_add {x : BitVec 64} (h : (x &&& 15#64 == 0#64) = true) (k : Nat) (hk : k % 16 = 0) :
    (x + BitVec.ofNat 64 k &&& 15#64) = 0#64 := by
  have h0 : x &&& 15#64 = 0#64 := by simpa using h
  have h1 := congrArg BitVec.toNat h0
  rw [and15_toNat] at h1
  apply BitVec.eq_of_toNat_eq
  rw [and15_toNat]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_zero] at h1 ⊢
  omega

end X25519Dalek.EMulB
end

section
/-! # Relocated `BL` words and calls to other blocks -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

theorem beq_false_of_mask {w K A M C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A &&& M) :
    (w &&& M == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, ← hK, BitVec.and_assoc, BitVec.and_comm M K, ← BitVec.and_assoc]

theorem beq_false_of_mask' {w K A C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A) :
    (w == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, hK]

theorem decode_bl_class (w : BitVec 32) (hK : w &&& 0xfc000000#32 = 0x94000000#32) :
    decode w = some (.bl ((w.extractLsb' 0 26).signExtend 64 <<< 2)) := by
  have h7c : (w &&& 0x7c000000#32 == 0x14000000#32) = true := by
    have : w &&& 0x7c000000#32 = (w &&& 0xfc000000#32) &&& 0x7c000000#32 := by
      rw [BitVec.and_assoc]; rfl
    rw [this, hK]; rfl
  have h31 : w.getLsbD 31 = true := by
    have := congrArg (fun x => x.getLsbD 31) hK
    simp only [BitVec.getLsbD_and] at this
    simpa using this
  rw [decode]
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
    beq_false_of_mask hK (C := 0x13800000#32) (M := 0x7f800000#32) (by decide), h7c, h31]
  simp

theorem hi_bits27 (D : BitVec 64) (h1 : -(2^27:Int) ≤ D.toInt) (h2 : D.toInt < 2^27) :
    ∀ i, 27 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 27 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  by_cases hs : 2 * D.toNat < 2 ^ 64
  · rw [if_pos hs] at h2
    have hD : D.toNat < 2 ^ 27 := by omega
    have g : ∀ j, 27 ≤ j → D.getLsbD j = false := fun j hj =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hD (Nat.pow_le_pow_right (by norm_num) hj))
    rw [g i hi1, g 27 le_rfl]
  · rw [if_neg hs] at h1
    have hE : (~~~D).toNat < 2 ^ 27 := by rw [BitVec.toNat_not]; omega
    have g : ∀ j, 27 ≤ j → j < 64 → D.getLsbD j = true := by
      intro j hj1 hj2
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hE (Nat.pow_le_pow_right (by norm_num) hj1))
      have e : (~~~D).getLsbD j = false := this
      rw [BitVec.getLsbD_not] at e
      simpa [hj2] using e
    rw [g i hi1 hi2, g 27 le_rfl (by norm_num)]

theorem lo_bits2 (D : BitVec 64) (h : D.toNat % 4 = 0) : ∀ i, i < 2 → D.getLsbD i = false := by
  intro i hi
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  generalize D.toNat = n at h ⊢
  interval_cases i <;> simp <;> omega

theorem bw_mask (D : BitVec 64) :
    ((0x94000000#32 &&& 0xfc000000#32) ||| ((D >>> 2).setWidth 32 &&& 0x03ffffff#32)) &&&
      0xfc000000#32 = 0x94000000#32 := by
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc ((D >>> 2).setWidth 32)]
  simp

theorem cbits (j : Nat) (hj : j < 26) : (0x94000000#32 : BitVec 32).getLsbD j = false ∧
    (0x03ffffff#32 : BitVec 32).getLsbD j = true := by
  interval_cases j <;> decide

theorem bw_off (D : BitVec 64) (hlo : ∀ i, i < 2 → D.getLsbD i = false)
    (hhi : ∀ i, 27 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 27) :
    ((((0x94000000#32 &&& 0xfc000000#32) ||| ((D >>> 2).setWidth 32 &&& 0x03ffffff#32))).extractLsb' 0 26).signExtend 64 <<< 2 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.msb_eq_getLsbD_last]
  rcases (show i < 2 ∨ (2 ≤ i ∧ i < 28) ∨ 28 ≤ i by omega) with h | ⟨h1, h2⟩ | h
  · simp [h, hlo i h]
  · have c := cbits (i - 2) (by omega)
    simp [hi, show ¬ i < 2 by omega, show i - 2 < 26 by omega, show i - 2 < 32 by omega]
    simp only [← BitVec.getLsbD_eq_getElem, c.1, c.2, Bool.false_and, Bool.false_or, Bool.and_true]
    simp [show i - 2 < 64 by omega]; congr 1; omega
  · have c := cbits 25 (by omega)
    simp [hi, show ¬ i < 2 by omega, show ¬ i - 2 < 26 by omega, c.1, c.2]
    simp only [← BitVec.getLsbD_eq_getElem]
    rw [hhi i (by omega) hi]
    simp [show i - 2 < 64 by omega]

/-- A relocated `bl` decodes to a branch-with-link whose offset reaches the target, when the
target is in range. -/
theorem decode_branchWord (place target : BitVec 64) (h : BranchInRange place target) :
    decode (branchWord 0x94000000#32 place target) = some (.bl (target - place)) := by
  unfold branchWord
  rw [decode_bl_class _ (bw_mask _)]
  congr 2
  exact bw_off _ (lo_bits2 _ h.1) (hi_bits27 _ h.2.1 h.2.2)

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

/-- The patched word of a `bl` to another block's function: a branch word to that function. -/
theorem patchedWord_call (i : Nat) (mpl : MultiPlacement) {off j offj : Nat} {name : String}
    (h : (blk i).relocAt? off = some { off := off, kind := .call26, sym := name } ∧
      (blk i).relaxableAt off = false ∧ (off < 4 ∨ (blk i).relaxableAt (off - 4) = false) ∧
      lookup name (blk i).symbols = none ∧ (blk i).weakRefs = [] ∧
      (blk i).wordAt off = 0x94000000#32)
    (hlk : lookupBlockSym name x25519CliMultiLib.blocks = some (j, offj)) :
    (blk i).patchedWord (x25519CliMultiLib.blockPlacement mpl i) off =
      branchWord 0x94000000#32 (mpl.base i + BitVec.ofNat 64 off) (mpl.base j + BitVec.ofNat 64 offj) := by
  obtain ⟨hr, hra, hra4, hsym, hweak, hw⟩ := h
  have h4 : (4 ≤ off && (blk i).relaxedAt (x25519CliMultiLib.blockPlacement mpl i) (off - 4)) = false := by
    rcases hra4 with h | h
    · simp; omega
    · simp [CodeBlock.relaxedAt, h]
  simp only [CodeBlock.patchedWord, hr, CodeBlock.relaxedAt, hra, Bool.false_and, Bool.false_eq_true,
    if_false]
  simp only [CodeBlock.relaxedAt] at h4
  rw [if_neg (by simp [h4])]
  simp only [RelocKind.isGotOrTlsIe, Bool.false_and, Bool.false_eq_true, if_false,
    CodeBlock.undefWeakBranch, hweak, List.contains_nil, CodeBlock.relocTarget, CodeBlock.b2bNext?,
    hsym, CodeBlock.target, CodeBlock.resolve, addSignedAddr, patchRelocWord, hw,
    MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, hlk]
  split
  · rename_i heq; split at heq <;> simp at heq
  · simp

/-- Fetching the relocated `bl` at offset `off` of block `i`, calling the function at offset
`offj` of block `j`. -/
theorem fetch_bl {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {i : Nat} (hi : i < 19) (k : Nat) {off j offj : Nat}
    {name : String}
    (hoff : off % 4 = 0 ∧ off + 4 ≤ (blk i).code.length)
    (h : (blk i).relocAt? off = some { off := off, kind := .call26, sym := name } ∧
      (blk i).relaxableAt off = false ∧ (off < 4 ∨ (blk i).relaxableAt (off - 4) = false) ∧
      lookup name (blk i).symbols = none ∧ (blk i).weakRefs = [] ∧
      (blk i).wordAt off = 0x94000000#32)
    (hlk : lookupBlockSym name x25519CliMultiLib.blocks = some (j, offj))
    {m : Memory} (hk : m0.KeepsFrozen m) :
    (bprog mpl k).fetchMem m (mpl.base i + BitVec.ofNat 64 off) =
      some (.bl ((mpl.base j + BitVec.ofNat 64 offj) - (mpl.base i + BitVec.ofNat 64 off))) := by
  have hCL' := libCodeLoaded_keepsFrozen hCL hk i (by rw [blocks_length]; exact hi)
  rw [fetch_word hP hi hCL' hoff.1 hoff.2 _ (hook_none mpl k), patchedWord_call i mpl h hlk]
  apply decode_branchWord
  have hPl := blk_placeable hP hi
  have hmem : ({ off := off, kind := .call26, sym := name } : RelocEntry) ∈ (blk i).relocs := by
    have := h.1
    simp only [CodeBlock.relocAt?] at this
    exact List.mem_of_find?_eq_some this
  have := (hPl.relocs_ok _ hmem).2.2
  simp only [CodeBlock.relocInRange, CodeRelocInRange] at this
  have ht : (blk i).relocTarget (x25519CliMultiLib.blockPlacement mpl i) off
      { off := off, kind := .call26, sym := name } = mpl.base j + BitVec.ofNat 64 offj := by
    obtain ⟨_, _, _, hsym, _, _⟩ := h
    simp only [CodeBlock.relocTarget, CodeBlock.b2bNext?, hsym, CodeBlock.target, CodeBlock.resolve,
      addSignedAddr, MultiPlacedLib.blockPlacement, MultiPlacedLib.resolve, hlk]
    split
    · rename_i heq; split at heq <;> simp at heq
    · simp
  rw [ht] at this
  exact this

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

/-- Running a call to another function of the library, from its contract `fnOk`: the caller
continues from any state the callee may return in. -/
theorem Reach.call {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) (k : Nat)
    {S α : Type} [ToBaseSpec S α] {name : String} {spec : MultiPlacement → S} {j offj : Nat}
    (hok : fnOk name spec) (hlk : lookupBlockSym name x25519CliMultiLib.blocks = some (j, offj))
    (hj : j < 19) {s : State} {Q : State → Prop} (x : α) (R' : SepProp)
    (hpc : s.pc = mpl.base j + BitVec.ofNat 64 offj) (hrun : s.status = .Running)
    (hal : s.spAligned = true) (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem)
    (hpre : s.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).pre x s ∗ R')
    (hpanic : ∀ sf, ¬ (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).onPanic x s sf ∗ R'))
    (hexit : ∀ c sf, ¬ (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).onExit x c s sf ∗ R'))
    (hoom : ∀ sf, ¬ (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).onOom x s sf ∗ R'))
    (hcont : ∀ sf, sf.pc = s.readReg64 Reg.lr → sf.sp = s.sp → sf.status = .Running →
      CalleeSavedPreserved s sf →
      (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).post x s sf ∗ R') →
      s.mem.KeepsFrozen sf.mem → Reach (bprog mpl k) sf Q) :
    Reach (bprog mpl k) s Q := by
  obtain ⟨j', off', hlk', hall⟩ := hok
  rw [hlk] at hlk'
  cases hlk'
  have hfa : x25519CliMultiLib.fnAddr mpl name = mpl.base j + BitVec.ofNat 64 offj := by
    simp [MultiPlacedLib.fnAddr, hlk]
  have hpre' : s.mem ⊨ (x25519CliMultiLib.withCodeLoaded mpl
      (ToBaseSpec.toSpec (spec mpl) (mpl.base j))).pre x s ∗ R' := by
    simp only [MultiPlacedLib.withCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, sat_pure_sep]
    exact ⟨hCL, hpre⟩
  obtain ⟨sf, hst, hout⟩ := hall mpl hP x R' s (by rw [hpc, hfa]) hrun hpre' hal
    (hCL j (by rw [blocks_length]; exact hj))
  have hkf := X25519Dalek.steps_keepsFrozen_v2 hst
  have hst' : Steps (bprog mpl k) s sf := bsteps_transfer (i := j) hst
  rcases hout with ⟨⟨hpcf, hspf, hrunf⟩, ⟨_, hcs⟩, hpost⟩ | ⟨_, hp⟩ | ⟨c, _, hp⟩ | ⟨_, hp⟩
  · exact Reach.steps hst' (hcont sf hpcf hspf hrunf hcs hpost hkf)
  · exact absurd hp (hpanic sf)
  · exact absurd hp (hexit c sf)
  · exact absurd hp (hoom sf)

theorem not_sat_false {m : Memory} {R : SepProp} : ¬ (m ⊨ (⌜False⌝ : SepProp) ∗ R) := by
  rw [sat_pure_sep]; exact fun h => h.1

end X25519Dalek.EMulB
end

section
/-! # Stack frames as lists of 64-bit words

`a ↦₆₄* ws` owns the words `ws` at `a, a + 8, …`; indexed reads and writes; conversions to and
from byte slices and `memRegion`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64

theorem words_cons (a w : BitVec 64) (ws : List (BitVec 64)) :
    (a ↦₆₄* (w :: ws)) = (a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄* ws) := rfl

theorem words_nil (a : BitVec 64) : (a ↦₆₄* ([] : List (BitVec 64))) = emp := rfl

theorem words_eq_bytes : ∀ (a : BitVec 64) (ws : List (BitVec 64)),
    (a ↦₆₄* ws) = (a ↦ₛ ws.flatMap unpack64)
  | a, [] => by rw [words_nil]; rfl
  | a, w :: ws => by
    rw [words_cons, words_eq_bytes (a + 8#64) ws, List.flatMap_cons, pointsToBytes_append,
      pointsTo64_eq_bytes]
    rfl

theorem addr8 (a : BitVec 64) (i : Nat) :
    a + 8#64 + BitVec.ofNat 64 (8 * i) = a + BitVec.ofNat 64 (8 * (i + 1)) := by
  rw [BitVec.add_assoc]; congr 1; bv_omega

theorem sat_words_read : ∀ {m : Memory} {a : BitVec 64} {ws : List (BitVec 64)} {F : SepProp},
    (m ⊨ (a ↦₆₄* ws) ∗ F) → ∀ (i : Nat) (hi : i < ws.length),
      m.read64 (a + BitVec.ofNat 64 (8 * i)) = ws[i] ∧
      m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true ∧
      m.canWrite (a + BitVec.ofNat 64 (8 * i)) 8 = true
  | _, _, [], _, _, i, hi => by simp at hi
  | m, a, w :: ws, F, hs, 0, _ => by
    rw [words_cons, sepConj_assoc] at hs
    simpa using sat64_read hs
  | m, a, w :: ws, F, hs, i + 1, hi => by
    rw [words_cons, sepConj_assoc, sepConj_left_comm] at hs
    have := sat_words_read hs i (by simp at hi; omega)
    rw [addr8] at this
    simpa using this

theorem sat_words_write : ∀ {m : Memory} {a : BitVec 64} {ws : List (BitVec 64)} {F : SepProp},
    (m ⊨ (a ↦₆₄* ws) ∗ F) → ∀ (i : Nat) (hi : i < ws.length) (w : BitVec 64),
      (m.write64 (a + BitVec.ofNat 64 (8 * i)) w ⊨ (a ↦₆₄* ws.set i w) ∗ F) ∧
      m.KeepsFrozen (m.write64 (a + BitVec.ofNat 64 (8 * i)) w)
  | _, _, [], _, _, i, hi, _ => by simp at hi
  | m, a, v :: ws, F, hs, 0, _, w => by
    rw [words_cons, sepConj_assoc] at hs
    have h := cell_write hs w
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.set_cons_zero]
    rw [words_cons, sepConj_assoc]
    exact ⟨h.2.2, h.2.1⟩
  | m, a, v :: ws, F, hs, i + 1, hi, w => by
    rw [words_cons, sepConj_assoc, sepConj_left_comm] at hs
    have := sat_words_write hs i (by simp at hi; omega) w
    rw [addr8] at this
    rw [List.set_cons_succ, words_cons, sepConj_assoc, sepConj_left_comm]
    exact this

/-- The 64-bit little-endian words of a byte list, eight bytes at a time. -/
def chunks64 : List (BitVec 8) → Nat → List (BitVec 64)
  | _, 0 => []
  | bs, k + 1 => pack64 (bs.take 8) :: chunks64 (bs.drop 8) k

theorem chunks64_length (bs : List (BitVec 8)) (k : Nat) : (chunks64 bs k).length = k := by
  induction k generalizing bs with
  | zero => rfl
  | succ k ih => simp [chunks64, ih]

theorem chunks64_flat : ∀ (k : Nat) (bs : List (BitVec 8)), bs.length = 8 * k →
    (chunks64 bs k).flatMap unpack64 = bs
  | 0, bs, h => by simp at h; simp [chunks64, h]
  | k + 1, bs, h => by
    simp only [chunks64, List.flatMap_cons]
    rw [unpack64_pack64 _ (by simp; omega), chunks64_flat k (bs.drop 8) (by simp; omega),
      List.take_append_drop]

theorem memRegion_words (a : BitVec 64) (k : Nat) (hk : 8 * k < 2 ^ 64) :
    memRegion a (8 * k) ⊢ ∃∗ ws, ⌜ws.length = k⌝ ∗ (a ↦₆₄* ws) := by
  intro h hh
  obtain ⟨bs, hb⟩ := memRegion_entails_bytes a (8 * k) hk h hh
  obtain ⟨hl, hb⟩ := pure_sepConj_holds.mp hb
  refine ⟨chunks64 bs k, pure_sepConj_holds.mpr ⟨chunks64_length bs k, ?_⟩⟩
  rw [words_eq_bytes, chunks64_flat k bs hl]
  exact hb

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

@[simp] theorem extract_lo128 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [hi']

@[simp] theorem extract_hi128 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  have : ¬ (64 + i < 64) := by omega
  simp [hi', this]

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem zext12_lit (n : Nat) : BitVec.zeroExtend 64 (BitVec.ofNat 12 n) = BitVec.ofNat 64 (n % 4096) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

theorem zext16_lit (n : Nat) : BitVec.zeroExtend 64 (BitVec.ofNat 16 n) = BitVec.ofNat 64 (n % 65536) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

@[simp] theorem bf_beq_1 : (BitfieldOp.BFM == BitfieldOp.UBFM) = false := by decide
@[simp] theorem bf_beq_2 : (BitfieldOp.BFM == BitfieldOp.SBFM) = false := by decide
@[simp] theorem bf_beq_3 : (BitfieldOp.UBFM == BitfieldOp.SBFM) = false := by decide
@[simp] theorem bf_beq_4 : (BitfieldOp.SBFM == BitfieldOp.UBFM) = false := by decide
@[simp] theorem bf_beq_5 : (BitfieldOp.UBFM == BitfieldOp.UBFM) = true := by decide
@[simp] theorem bf_beq_6 : (BitfieldOp.SBFM == BitfieldOp.SBFM) = true := by decide

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

/-- After a 64-bit store into an owned word list, continue from an abstract memory. -/
theorem Reach.wr64 {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {vr : BitVec 5 → BitVec 128} {Q : State → Prop}
    {base a : BitVec 64} {ws : List (BitVec 64)} {F : SepProp} {v : BitVec 64} (i : Nat)
    (hs : m ⊨ (base ↦₆₄* ws) ∗ F) (ha : a = base + BitVec.ofNat 64 (8 * i)) (hi : i < ws.length)
    (h : ∀ m', (m' ⊨ (base ↦₆₄* ws.set i v) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc r sp ps m' vr) Q) :
    Reach p (mkS s0 pc r sp ps (m.write64 a v) vr) Q := by
  subst ha
  obtain ⟨h1, h2⟩ := sat_words_write hs i hi v
  exact h _ h1 h2

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem add_sub_cancel' (a b : BitVec 64) : a + (b - a) = b := by bv_omega
theorem sub_add_cancel' (a : BitVec 64) (k : Nat) : a - BitVec.ofNat 64 k + BitVec.ofNat 64 k = a := by
  bv_omega

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem memRegion_bytes (a : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) {m : Memory} {F : SepProp}
    (hs : m ⊨ memRegion a n ∗ F) : ∃ bs, bs.length = n ∧ (m ⊨ (a ↦ₛ bs) ∗ F) := by
  have h := sat_sep_mono hs (memRegion_entails_bytes a n hn)
  rw [sepExists_sepConj, sat_sepExists] at h
  obtain ⟨bs, h⟩ := h
  rw [sepConj_assoc, sat_pure_sep] at h
  exact ⟨bs, h.1, h.2⟩

theorem memRegion_words' (a : BitVec 64) (k : Nat) (hk : 8 * k < 2 ^ 64) {m : Memory} {F : SepProp}
    (hs : m ⊨ memRegion a (8 * k) ∗ F) : ∃ ws, ws.length = k ∧ (m ⊨ (a ↦₆₄* ws) ∗ F) := by
  have h := sat_sep_mono hs (memRegion_words a k hk)
  rw [sepExists_sepConj, sat_sepExists] at h
  obtain ⟨ws, h⟩ := h
  rw [sepConj_assoc, sat_pure_sep] at h
  exact ⟨ws, h.1, h.2⟩

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem Reach.wr64x2 {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {vr : BitVec 5 → BitVec 128} {Q : State → Prop}
    {base a b : BitVec 64} {ws : List (BitVec 64)} {F : SepProp} {v w : BitVec 64} (i : Nat)
    (hs : m ⊨ (base ↦₆₄* ws) ∗ F) (ha : a = base + BitVec.ofNat 64 (8 * i))
    (hb : b = base + BitVec.ofNat 64 (8 * (i + 1))) (hi : i + 1 < ws.length)
    (h : ∀ m', (m' ⊨ (base ↦₆₄* (ws.set i v).set (i + 1) w) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc r sp ps m' vr) Q) :
    Reach p (mkS s0 pc r sp ps ((m.write64 a v).write64 b w) vr) Q := by
  subst ha
  obtain ⟨h1, k1⟩ := sat_words_write hs i (by omega) v
  exact Reach.wr64 (i + 1) h1 hb (by simp; omega) (fun m' h' k' => h m' h' (k1.trans k'))

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64 Arm64.Obj

/-- Callee-saved general registers of `sf` agree with the register function `rf`. -/
def CSRegs (sf : State) (rf : BitVec 5 → BitVec 64) : Prop :=
  sf.regs.regs 19#5 = rf 19#5 ∧ sf.regs.regs 20#5 = rf 20#5 ∧ sf.regs.regs 21#5 = rf 21#5 ∧
  sf.regs.regs 22#5 = rf 22#5 ∧ sf.regs.regs 23#5 = rf 23#5 ∧ sf.regs.regs 24#5 = rf 24#5 ∧
  sf.regs.regs 25#5 = rf 25#5 ∧ sf.regs.regs 26#5 = rf 26#5 ∧ sf.regs.regs 27#5 = rf 27#5 ∧
  sf.regs.regs 28#5 = rf 28#5 ∧ sf.regs.regs 29#5 = rf 29#5

/-- A call from an abstract state: the caller continues from the callee's return state. -/
theorem Reach.callS {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) (k : Nat)
    {S α : Type} [ToBaseSpec S α] {name : String} {spec : MultiPlacement → S} {j offj : Nat}
    (hok : fnOk name spec) (hlk : lookupBlockSym name x25519CliMultiLib.blocks = some (j, offj))
    (hj : j < 19) {s0 : State} {pc : BitVec 64} {rf : BitVec 5 → BitVec 64} {sp : BitVec 64}
    {ps : PState} {m : Memory} {vf : BitVec 5 → BitVec 128} {Q : State → Prop} (x : α) (R' : SepProp)
    (hpc : pc = mpl.base j + BitVec.ofNat 64 offj) (hrun : s0.status = .Running)
    (hal : (sp &&& 15#64) = 0#64) (hCL : x25519CliMultiLib.CodeLoaded mpl m)
    (hpre : m ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).pre x (mkS s0 pc rf sp ps m vf) ∗ R')
    (hpanic : ∀ sf, ¬ (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).onPanic x
      (mkS s0 pc rf sp ps m vf) sf ∗ R'))
    (hexit : ∀ c sf, ¬ (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).onExit x c
      (mkS s0 pc rf sp ps m vf) sf ∗ R'))
    (hoom : ∀ sf, ¬ (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).onOom x
      (mkS s0 pc rf sp ps m vf) sf ∗ R'))
    (hcont : ∀ sf, sf.status = .Running → sf.sp = sp → CSRegs sf rf →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨vf⟩ →
      (sf.mem ⊨ (ToBaseSpec.toSpec (spec mpl) (mpl.base j)).post x (mkS s0 pc rf sp ps m vf) sf ∗ R') →
      m.KeepsFrozen sf.mem →
      Reach (bprog mpl k) (mkS sf (rf 30#5) sf.regs.regs sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl k) (mkS s0 pc rf sp ps m vf) Q := by
  refine Reach.call hP k hok hlk hj x R' hpc hrun (by simp [hal]) hCL hpre hpanic hexit hoom ?_
  intro sf hpcf hspf hrunf hcs hpost hkf
  have hpc' : sf.pc = rf 30#5 := by rw [hpcf]; simp [Reg.lr]
  have hsp' : sf.sp = sp := by rw [hspf]; rfl
  have e : sf = mkS sf (rf 30#5) sf.regs.regs sp sf.pstate sf.mem sf.vregs.regs := by
    rw [← hpc', ← hsp']; rfl
  rw [e]
  obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, cfp, cv⟩ := hcs
  simp only [mkS_readGpr, Reg.fp, BitVec.reduceEq, ite_false] at c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 cfp
  rw [readGpr_eq sf _ (by decide)] at c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 cfp
  exact hcont sf hrunf hsp' ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, cfp⟩ cv hpost hkf

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

theorem Reach.wr64x4 {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {vr : BitVec 5 → BitVec 128} {Q : State → Prop}
    {base a0 a1 a2 a3 : BitVec 64} {ws : List (BitVec 64)} {F : SepProp} {v0 v1 v2 v3 : BitVec 64}
    (i : Nat) (hs : m ⊨ (base ↦₆₄* ws) ∗ F) (h0 : a0 = base + BitVec.ofNat 64 (8 * i))
    (h1 : a1 = base + BitVec.ofNat 64 (8 * (i + 1))) (h2 : a2 = base + BitVec.ofNat 64 (8 * (i + 2)))
    (h3 : a3 = base + BitVec.ofNat 64 (8 * (i + 3))) (hi : i + 3 < ws.length)
    (h : ∀ m', (m' ⊨ (base ↦₆₄* (((ws.set i v0).set (i + 1) v1).set (i + 2) v2).set (i + 3) v3) ∗ F) →
      m.KeepsFrozen m' → Reach p (mkS s0 pc r sp ps m' vr) Q) :
    Reach p (mkS s0 pc r sp ps ((((m.write64 a0 v0).write64 a1 v1).write64 a2 v2).write64 a3 v3) vr) Q := by
  subst h0 h1
  obtain ⟨g1, k1⟩ := sat_words_write hs i (by omega) v0
  obtain ⟨g2, k2⟩ := sat_words_write g1 (i + 1) (by simp; omega) v1
  exact Reach.wr64x2 (i + 2) g2 h2 h3 (by simp; omega) (fun m' h' k' => h m' h' (k1.trans (k2.trans k')))

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB
open Arm64

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB

end X25519Dalek.EMulB
end

section
/-! # Block 13: one `Reach` lemma per instruction shape (generated by tools/gen_shp.py)

Each lemma runs one instruction of a given shape from an abstract state `mkS s0 pc r sp ps m v`
(the pattern of the sibling ladder proof's `Shapes.lean`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64

section
variable {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem y_addi_sp {d : BitVec 5} {k : BitVec 12} {pc' : BitVec 64} (hd : d ≠ 31#5) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .ADD (.gpr d) .sp k false))
    (h : Reach p (mkS s0 pc' (upd r d (sp + k.setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd]
  exact h

theorem y_subsp {k : BitVec 12} {pc' : BitVec 64}  (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUB .sp .sp k false))
    (h : Reach p (mkS s0 pc' r (sp - k.setWidth 64) ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', BitVec.truncate_eq_setWidth]
  exact h

theorem y_mov {d b : BitVec 5} {pc' : BitVec 64} (hd : d ≠ 31#5) (hb : b ≠ 31#5) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W64 .ORR (.gpr d) .xzr (.gpr b) .LSL 0))
    (h : Reach p (mkS s0 pc' (upd r d (r b)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, hb, BitVec.zero_or]
  exact h

theorem y_movzr {d : BitVec 5} {pc' : BitVec 64} (hd : d ≠ 31#5) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W64 .ORR (.gpr d) .xzr .xzr .LSL 0))
    (h : Reach p (mkS s0 pc' (upd r d 0#64) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd]
  exact h

theorem y_movz32 {d : BitVec 5} {k : BitVec 16} {pc' : BitVec 64} (hd : d ≠ 31#5) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.moveWide .W32 .MOVZ (.gpr d) k 0))
    (h : Reach p (mkS s0 pc' (upd r d (((k.setWidth 64).setWidth 32).setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd]
  exact h

theorem y_cmpi {n : BitVec 5} {k : BitVec 12} {pc' : BitVec 64} (hn : n ≠ 31#5) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUBS .xzr (.gpr n) k false))
    (h : Reach p (mkS s0 pc' r sp (AddWithCarry64 (r n) (~~~(k.setWidth 64)) true).2 m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hn]
  exact h

theorem y_bcond_t {c : CondCode} {off : BitVec 64} {pc' : BitVec 64} (hc : ConditionHolds c ps = true) (hpc : pc + off = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.bCond c off))
    (h : Reach p (mkS s0 pc' r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, mkS_pstate, mkS_pc, mkS_setPC, mkS_advancePC, hc, ite_true, Bool.false_eq_true, ite_false]
  exact h

theorem y_bl {off : BitVec 64} {pc' : BitVec 64} {lr : BitVec 64}  (hpc : pc + off = pc') (hlr : pc + 4#64 = lr) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.bl off))
    (h : Reach p (mkS s0 pc' (upd r 30#5 lr) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; subst hlr; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', Bool.true_eq]
  exact h

theorem y_movi0  {pc' : BitVec 64}  (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.simdImmShift true true 0#4 0#3 0x1c#5 0#5 0#5))
    (h : Reach p (mkS s0 pc' r sp ps m (upd v 0#5 0#128)) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', Bool.true_eq]
  exact h

theorem y_stp_sp {t1 t2 : BitVec 5} {off A A8 : BitVec 64} {pc' : BitVec 64} (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (hA8 : A + 8#64 = A8) (c1 : m.canWrite A 8 = true) (c2 : m.canWrite A8 8 = true) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stp .W64 (.gpr t1) (.gpr t2) (.Offset .sp off)))
    (h : Reach p (mkS s0 pc' r sp ps ((m.write64 A (r t1)).write64 A8 (r t2)) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', ht1, ht2, hal, hA, hA8, c1, c2]
  exact h

theorem y_str_sp {t : BitVec 5} {off A : BitVec 64} {pc' : BitVec 64} (ht : t ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (c : m.canWrite A 8 = true) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .X64 (.gpr t) (.Offset .sp off)))
    (h : Reach p (mkS s0 pc' r sp ps (m.write64 A (r t)) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', ht, hal, hA, c]
  exact h

theorem y_strz_sp {off A : BitVec 64} {pc' : BitVec 64} (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (c : m.canWrite A 8 = true) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .X64 .xzr (.Offset .sp off)))
    (h : Reach p (mkS s0 pc' r sp ps (m.write64 A 0#64) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hal, hA, c]
  exact h

theorem y_stp_pre {t1 t2 : BitVec 5} {off A A8 : BitVec 64} {pc' : BitVec 64} (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (hA8 : A + 8#64 = A8) (c1 : m.canWrite A 8 = true) (c2 : m.canWrite A8 8 = true) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stp .W64 (.gpr t1) (.gpr t2) (.PreIndex .sp off)))
    (h : Reach p (mkS s0 pc' r A ps ((m.write64 A (r t1)).write64 A8 (r t2)) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', ht1, ht2, hal, hA, hA8, c1, c2]
  exact h

theorem y_ldpq_o {t1 t2 b : BitVec 5} {off A A16 lo1 hi1 lo2 hi2 : BitVec 64} {pc' : BitVec 64} (hb : b ≠ 31#5) (hA : r b + off = A) (hA16 : A + 16#64 = A16) (c1 : m.canRead A 16 = true) (c2 : m.canRead A16 16 = true) (e1 : m.read64 A = lo1) (e2 : m.read64 (A + 8#64) = hi1) (e3 : m.read64 A16 = lo2) (e4 : m.read64 (A16 + 8#64) = hi2) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldpSimd .Q128 t1 t2 (.Offset (.gpr b) off)))
    (h : Reach p (mkS s0 pc' r sp ps m (upd (upd v t1 (hi1 ++ lo1)) t2 (hi2 ++ lo2))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hb, hA, hA16, c1, c2, e1, e2, e3, e4]
  exact h

theorem y_stpq_sp {t1 t2 : BitVec 5} {off A A8 A16 A24 lo1 hi1 lo2 hi2 : BitVec 64} {pc' : BitVec 64} (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (hA8 : A + 8#64 = A8) (hA16 : A + 16#64 = A16) (hA24 : A16 + 8#64 = A24) (c1 : m.canWrite A 16 = true) (c2 : m.canWrite A16 16 = true) (ev1 : v t1 = hi1 ++ lo1) (ev2 : v t2 = hi2 ++ lo2) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stpSimd .Q128 t1 t2 (.Offset .sp off)))
    (h : Reach p (mkS s0 pc' r sp ps ((((m.write64 A lo1).write64 A8 hi1).write64 A16 lo2).write64 A24 hi2) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hal, hA, hA8, hA16, hA24, c1, c2, ev1, ev2]
  exact h

theorem y_strq_u {t b : BitVec 5} {off A A8 lo hi : BitVec 64} {pc' : BitVec 64} (hb : b ≠ 31#5) (hA : r b + off = A) (hA8 : A + 8#64 = A8) (c : m.canWrite A 16 = true) (ev : v t = hi ++ lo) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.strSimd .Q128 t (.UnscaledOffset (.gpr b) off)))
    (h : Reach p (mkS s0 pc' r sp ps ((m.write64 A lo).write64 A8 hi) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hb, hA, hA8, c, ev]
  exact h

theorem y_strq_usp {t : BitVec 5} {off A A8 lo hi : BitVec 64} {pc' : BitVec 64} (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (hA8 : A + 8#64 = A8) (c : m.canWrite A 16 = true) (ev : v t = hi ++ lo) (hpc : pc + 4#64 = pc') (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.strSimd .Q128 t (.UnscaledOffset .sp off)))
    (h : Reach p (mkS s0 pc' r sp ps ((m.write64 A lo).write64 A8 hi) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hal, hA, hA8, c, ev]
  exact h

end

end X25519Dalek.EMulB
end

section
/-! # Block 13: generic helpers (register and vector bookkeeping, callee frames, 128-bit copies) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

theorem cs_upd {v : BitVec 5 → BitVec 128} {i : BitVec 5} {x : BitVec 128} (hi : i.toNat < 8)
    {X : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    (h : VRegFile.calleeSaved ⟨v⟩ = X) : VRegFile.calleeSaved ⟨upd v i x⟩ = X := by
  rw [← h]
  have hne : ∀ k : BitVec 5, 8 ≤ k.toNat → (k = i) = False := fun k hk => by
    apply propext; constructor
    · intro e; subst e; omega
    · intro e; exact e.elim
  simp only [VRegFile.calleeSaved, VRegFile.read, upd_apply, hne 8#5 (by decide), hne 9#5 (by decide),
    hne 10#5 (by decide), hne 11#5 (by decide), hne 12#5 (by decide), hne 13#5 (by decide),
    hne 14#5 (by decide), hne 15#5 (by decide), if_false]

theorem aadd (S : BitVec 64) (a b c : Nat) (h : a + b = c) :
    S + BitVec.ofNat 64 a + BitVec.ofNat 64 b = S + BitVec.ofNat 64 c := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, h]

theorem addK (S : BitVec 64) (k : BitVec 12) (n : Nat) (h : k.setWidth 64 = BitVec.ofNat 64 n) :
    S + k.setWidth 64 = S + BitVec.ofNat 64 n := by rw [h]

theorem subK2 (S : BitVec 64) (a : Nat) (k : BitVec 12) (n : Nat) (h : n + k.toNat = a) :
    S + BitVec.ofNat 64 a - k.setWidth 64 = S + BitVec.ofNat 64 n := by
  have hk := k.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  have : k.toNat % 2 ^ 64 = k.toNat := Nat.mod_eq_of_lt (by omega)
  rw [this]; omega

theorem list20 {α : Type} (l : List α) (h : l.length = 20) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19, l = [a0, a1, a2, a3, a4,
      a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19] := by
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, rfl⟩

theorem pcA (b x y z : BitVec 64) (h : x + y = z) : b + x + y = b + z := by
  rw [BitVec.add_assoc, h]

/-- Abstract the register file after a write. -/
theorem Reach.absR {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}
    {d : BitVec 5} {t : BitVec 64}
    (h : ∀ r' : BitVec 5 → BitVec 64, (∀ k, k ≠ d → r' k = r k) → r' d = t →
      Reach p (mkS s0 pc r' sp ps m v) Q) :
    Reach p (mkS s0 pc (upd r d t) sp ps m v) Q :=
  h _ (fun _ hk => upd_ne r t hk) (upd_same r d t)

/-! ## 128-bit copies between word lists -/

theorem allPerm_add (m : Memory) (p : Option Perm → Bool) : ∀ (a : BitVec 64) (n k : Nat),
    m.allPerm p a (n + k) = (m.allPerm p a n && m.allPerm p (a + BitVec.ofNat 64 n) k)
  | a, 0, k => by simp [Memory.allPerm]
  | a, n + 1, k => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [Memory.allPerm, allPerm_add m p (a + 1#64) n k, Bool.and_assoc]
    congr 3
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

theorem allNoLazyFree_add (m : Memory) : ∀ (a : BitVec 64) (n k : Nat),
    m.allNoLazyFree a (n + k) = (m.allNoLazyFree a n && m.allNoLazyFree (a + BitVec.ofNat 64 n) k)
  | a, 0, k => by simp [Memory.allNoLazyFree]
  | a, n + 1, k => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [Memory.allNoLazyFree, allNoLazyFree_add m (a + 1#64) n k, Bool.and_assoc]
    congr 3
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

theorem canRead16 {m : Memory} {a : BitVec 64} (h1 : m.canRead a 8 = true)
    (h2 : m.canRead (a + 8#64) 8 = true) : m.canRead a 16 = true := by
  simp only [Memory.canRead, Bool.and_eq_true] at h1 h2 ⊢
  rw [show 16 = 8 + 8 from rfl, allPerm_add, allNoLazyFree_add]
  simp only [Bool.and_eq_true]
  exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩

theorem canWrite16 {m : Memory} {a : BitVec 64} (h1 : m.canWrite a 8 = true)
    (h2 : m.canWrite (a + 8#64) 8 = true) : m.canWrite a 16 = true := by
  simp only [Memory.canWrite] at h1 h2 ⊢
  rw [show 16 = 8 + 8 from rfl, allPerm_add]
  simp only [Bool.and_eq_true]
  exact ⟨h1, h2⟩

section
variable {p : Program} {s0 : State} {pc pc' : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem w8' (a : BitVec 64) (i : Nat) :
    a + BitVec.ofNat 64 (8 * i) + 8#64 = a + BitVec.ofNat 64 (8 * (i + 1)) := by
  rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
  congr 2

theorem w16' (a : BitVec 64) (i : Nat) :
    a + BitVec.ofNat 64 (8 * i) + 16#64 = a + BitVec.ofNat 64 (8 * (i + 2)) := by
  rw [BitVec.add_assoc, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
  congr 2

end

end X25519Dalek.EMulB
end

section
/-! # Block 13 calls of `Scalar::as_radix_16` and `EdwardsPoint::mul_by_pow_2` (k = 4) through their
published contracts -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

abbrev radName : String := "<curve25519_dalek::scalar::Scalar>::as_radix_16"

theorem lk_rad : lookupBlockSym radName x25519CliMultiLib.blocks = some (3, 0) := by decide +kernel

/-- A call of `Scalar::as_radix_16` (block 3, no stack): `out ← digits(a)`. -/
theorem call_rad {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {Q : State → Prop}
    {s0 : State} {pc : BitVec 64} {rf : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState}
    {m : Memory} {vf : BitVec 5 → BitVec 128} {out a : BitVec 64} {O A : List (BitVec 8)} {R : SepProp}
    (hpc : pc = mpl.base 3 + BitVec.ofNat 64 0) (hrun : s0.status = .Running)
    (hal : (sp &&& 15#64) = 0#64) (hCL : x25519CliMultiLib.CodeLoaded mpl m)
    (h0 : rf 0#5 = out) (h1 : rf 1#5 = a) (hO : O.length = 64) (hA : A.length = 32)
    (hA31 : (A.getD 31 0#8).toNat ≤ 127)
    (hm : m ⊨ (a ↦ₛ A) ∗ (out ↦ₛ O) ∗ R)
    (hcont : ∀ (sf : State), sf.status = .Running → sf.sp = sp →
      CSRegs sf rf → calleeSavedVRegs sf = VRegFile.calleeSaved ⟨vf⟩ →
      (sf.mem ⊨ (a ↦ₛ A) ∗ (out ↦ₛ scalarRadix16Digits A) ∗ R) → m.KeepsFrozen sf.mem →
      Reach (bprog mpl 13) (mkS sf (rf 30#5) sf.regs.regs sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl 13) (mkS s0 pc rf sp ps m vf) Q := by
  have hpre : m ⊨ (⌜(mkS s0 pc rf sp ps m vf).readReg64 Reg.x0 = out ∧
      (mkS s0 pc rf sp ps m vf).readReg64 Reg.x1 = a ∧ O.length = 64 ∧ A.length = 32 ∧
      (A.getD 31 0#8).toNat ≤ 127⌝ ∗ (a ↦ₛ A) ∗ (out ↦ₛ O)) ∗ R := by
    rw [sepConj_assoc, sat_pure_sep]
    exact ⟨⟨by simp [h0], by simp [h1], hO, hA, hA31⟩, by rw [← sepConj_assoc] at hm; exact hm⟩
  refine Reach.callS hP 13 fnOk_scalar_as_radix_16_v2 lk_rad (by decide) (out, a, O, A) R hpc hrun hal hCL
    hpre ?_ ?_ ?_ ?_
  · intro sf; exact not_sat_false
  · intro c sf; exact not_sat_false
  · intro sf; exact not_sat_false
  intro sf hrunf hspf hcs hv hpost hkf
  refine hcont sf hrunf hspf hcs hv ?_ hkf
  rw [← sepConj_assoc]; exact hpost

end X25519Dalek.EMulB
end

section
/-! # Block 13: per-offset instruction fetch (generated by tools/gen_code13.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

theorem blk13 : blk 13 = x25519CliBlk13 := rfl

theorem len13 : x25519CliBlk13.code.length = 668 := by decide +kernel

section
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m0) (j : Nat) {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem c13_0 : (bprog mpl j).fetchMem m (mpl.base 13) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.PreIndex (Reg.sp) 0xffffffffffffffa0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 0) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.PreIndex (Reg.sp) 0xffffffffffffffa0#64))) (by decide) rfl (by decide +kernel) hk
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

theorem c13_4 : (bprog mpl j).fetchMem m (mpl.base 13 + 4#64) =
    some (Instr.str (MemWidth.X64) (Reg.gpr 0x1c#5) (AddrMode.Offset (Reg.sp) 0x0000000000000010#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 4) (inst := (Instr.str (MemWidth.X64) (Reg.gpr 0x1c#5) (AddrMode.Offset (Reg.sp) 0x0000000000000010#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_8 : (bprog mpl j).fetchMem m (mpl.base 13 + 8#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 8) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_12 : (bprog mpl j).fetchMem m (mpl.base 13 + 12#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x18#5) (Reg.gpr 0x17#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 12) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x18#5) (Reg.gpr 0x17#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_16 : (bprog mpl j).fetchMem m (mpl.base 13 + 16#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x16#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 16) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x16#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_20 : (bprog mpl j).fetchMem m (mpl.base 13 + 20#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 20) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_24 : (bprog mpl j).fetchMem m (mpl.base 13 + 24#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x1d#5) (Reg.sp) 0x000#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 24) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x1d#5) (Reg.sp) 0x000#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_28 : (bprog mpl j).fetchMem m (mpl.base 13 + 28#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.sp) (Reg.sp) 0x2a0#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 28) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.sp) (Reg.sp) 0x2a0#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_32 : (bprog mpl j).fetchMem m (mpl.base 13 + 32#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x14#5) (Reg.xzr) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 32) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x14#5) (Reg.xzr) (Reg.gpr 0x00#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_36 : (bprog mpl j).fetchMem m (mpl.base 13 + 36#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x000#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 36) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x000#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_40 : (bprog mpl j).fetchMem m (mpl.base 13 + 40#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x13#5) (Reg.xzr) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 40) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x13#5) (Reg.xzr) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_44 : (bprog mpl j).fetchMem m (mpl.base 13 + 44#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x15#5) (Reg.sp) 0x0e8#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 44) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x15#5) (Reg.sp) 0x0e8#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_48 : (bprog mpl j).fetchMem m (mpl.base 13 + 48#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x18#5) (Reg.sp) 0x040#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 48) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x18#5) (Reg.sp) 0x040#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_52 : (bprog mpl j).fetchMem m (mpl.base 13 + 52#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x16#5) (Reg.sp) 0x000#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 52) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x16#5) (Reg.sp) 0x000#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_56 {j' offj : Nat} (hlk : lookupBlockSym radName x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 13 + 56#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 13 + BitVec.ofNat 64 56))) :=
  fetch_bl hP hCL (i := 13) (by decide) j (off := 56) (name := radName) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c13_60 : (bprog mpl j).fetchMem m (mpl.base 13 + 60#64) =
    some (Instr.simdImmShift true true 0x0#4 0x0#3 0x1c#5 0x00#5 0x00#5) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 60) (inst := (Instr.simdImmShift true true 0x0#4 0x0#3 0x1c#5 0x00#5 0x00#5)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_72 : (bprog mpl j).fetchMem m (mpl.base 13 + 72#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x02#5 (AddrMode.Offset (Reg.gpr 0x08#5) 0x0000000000000000#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 72) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x01#5 0x02#5 (AddrMode.Offset (Reg.gpr 0x08#5) 0x0000000000000000#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_76 : (bprog mpl j).fetchMem m (mpl.base 13 + 76#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x17#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 76) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x17#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_80 : (bprog mpl j).fetchMem m (mpl.base 13 + 80#64) =
    some (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x19#5) 0x03c0#16 0) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 80) (inst := (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x19#5) 0x03c0#16 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_84 : (bprog mpl j).fetchMem m (mpl.base 13 + 84#64) =
    some (Instr.str (MemWidth.X64) (Reg.xzr) (AddrMode.Offset (Reg.sp) 0x0000000000000060#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 84) (inst := (Instr.str (MemWidth.X64) (Reg.xzr) (AddrMode.Offset (Reg.sp) 0x0000000000000060#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_88 : (bprog mpl j).fetchMem m (mpl.base 13 + 88#64) =
    some (Instr.str (MemWidth.X64) (Reg.xzr) (AddrMode.Offset (Reg.sp) 0x0000000000000088#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 88) (inst := (Instr.str (MemWidth.X64) (Reg.xzr) (AddrMode.Offset (Reg.sp) 0x0000000000000088#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_92 : (bprog mpl j).fetchMem m (mpl.base 13 + 92#64) =
    some (Instr.strSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.gpr 0x18#5) 0x0000000000000078#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 92) (inst := (Instr.strSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.gpr 0x18#5) 0x0000000000000078#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_96 : (bprog mpl j).fetchMem m (mpl.base 13 + 96#64) =
    some (Instr.strSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.gpr 0x18#5) 0x0000000000000088#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 96) (inst := (Instr.strSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.gpr 0x18#5) 0x0000000000000088#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_100 : (bprog mpl j).fetchMem m (mpl.base 13 + 100#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x18#5) (Reg.sp) 0x188#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 100) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x18#5) (Reg.sp) 0x188#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_104 : (bprog mpl j).fetchMem m (mpl.base 13 + 104#64) =
    some (Instr.strSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.UnscaledOffset (Reg.sp) 0x0000000000000068#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 104) (inst := (Instr.strSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.UnscaledOffset (Reg.sp) 0x0000000000000068#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_108 : (bprog mpl j).fetchMem m (mpl.base 13 + 108#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 108) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x00#5 0x00#5 (AddrMode.Offset (Reg.sp) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_112 : (bprog mpl j).fetchMem m (mpl.base 13 + 112#64) =
    some (Instr.strSimd (SimdMemSize.Q128) 0x02#5 (AddrMode.UnscaledOffset (Reg.sp) 0x0000000000000078#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 112) (inst := (Instr.strSimd (SimdMemSize.Q128) 0x02#5 (AddrMode.UnscaledOffset (Reg.sp) 0x0000000000000078#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_116 : (bprog mpl j).fetchMem m (mpl.base 13 + 116#64) =
    some (Instr.str (MemWidth.X64) (Reg.xzr) (AddrMode.Offset (Reg.sp) 0x00000000000000b0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 116) (inst := (Instr.str (MemWidth.X64) (Reg.xzr) (AddrMode.Offset (Reg.sp) 0x00000000000000b0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_120 : (bprog mpl j).fetchMem m (mpl.base 13 + 120#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x02#5 (AddrMode.Offset (Reg.sp) 0x0000000000000090#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 120) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x01#5 0x02#5 (AddrMode.Offset (Reg.sp) 0x0000000000000090#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_124 : (bprog mpl j).fetchMem m (mpl.base 13 + 124#64) =
    some (Instr.str (MemWidth.X64) (Reg.xzr) (AddrMode.Offset (Reg.sp) 0x00000000000000d8#64)) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 124) (inst := (Instr.str (MemWidth.X64) (Reg.xzr) (AddrMode.Offset (Reg.sp) 0x00000000000000d8#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_128 : (bprog mpl j).fetchMem m (mpl.base 13 + 128#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x17#5) 0x040#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 128) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x17#5) 0x040#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c13_132 : (bprog mpl j).fetchMem m (mpl.base 13 + 132#64) =
    some (Instr.bCond (CondCode.NE) 0x0000000000000014#64) := by
  have := fetch_at' hP hCL (by decide) j blk13 len13 (off := 132) (inst := (Instr.bCond (CondCode.NE) 0x0000000000000014#64)) (by decide) rfl (by decide +kernel) hk
  exact this

end

end X25519Dalek.EMulB
end

section
/-! # Relocated `ADRP`/`ADD` (and their relaxed `NOP`/`ADR` form): loading a `.rodata` address

Decoding lemmas copied from the sibling batch's `Solutions/X25519DalekEdwards/Reloc.lean`, itself from
the zlib CRC-32 mission's `ZlibCrc32.Small.RelocBase`/`RelocTab`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

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

theorem decode_addimm_class (w : BitVec 32) (hK : w &&& 0x1f800000#32 = 0x11000000#32) :
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

theorem hi_bits32 (D : BitVec 64) (h1 : -(2^32:Int) ≤ D.toInt) (h2 : D.toInt < 2^32) :
    ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  by_cases hs : 2 * D.toNat < 2 ^ 64
  · rw [if_pos hs] at h2
    have hD : D.toNat < 2 ^ 32 := by omega
    have g : ∀ j, 32 ≤ j → D.getLsbD j = false := fun j hj =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hD (Nat.pow_le_pow_right (by norm_num) hj))
    rw [g i hi1, g 32 le_rfl]
  · rw [if_neg hs] at h1
    have hE : (~~~D).toNat < 2 ^ 32 := by rw [BitVec.toNat_not]; omega
    have g : ∀ j, 32 ≤ j → j < 64 → D.getLsbD j = true := by
      intro j hj1 hj2
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hE (Nat.pow_le_pow_right (by norm_num) hj1))
      have e : (~~~D).getLsbD j = false := this
      rw [BitVec.getLsbD_not] at e
      simpa [hj2] using e
    rw [g i hi1 hi2, g 32 le_rfl (by norm_num)]

theorem hi_bits20 (D : BitVec 64) (h1 : -(2^20:Int) ≤ D.toInt) (h2 : D.toInt < 2^20) :
    ∀ i, 20 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 20 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  by_cases hs : 2 * D.toNat < 2 ^ 64
  · rw [if_pos hs] at h2
    have hD : D.toNat < 2 ^ 20 := by omega
    have g : ∀ j, 20 ≤ j → D.getLsbD j = false := fun j hj =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hD (Nat.pow_le_pow_right (by norm_num) hj))
    rw [g i hi1, g 20 le_rfl]
  · rw [if_neg hs] at h1
    have hE : (~~~D).toNat < 2 ^ 20 := by rw [BitVec.toNat_not]; omega
    have g : ∀ j, 20 ≤ j → j < 64 → D.getLsbD j = true := by
      intro j hj1 hj2
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hE (Nat.pow_le_pow_right (by norm_num) hj1))
      have e : (~~~D).getLsbD j = false := this
      rw [BitVec.getLsbD_not] at e
      simpa [hj2] using e
    rw [g i hi1 hi2, g 20 le_rfl (by norm_num)]

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

theorem page_add_lo (T : BitVec 64) : pageOf T + (T.extractLsb' 0 12).setWidth 64 = T := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, pageOf_toNat]
  simp [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat]
  have := T.isLt; omega


theorem decode_nop : decode nopWord = some .nop := by decide


section words
variable (D : BitVec 64)

theorem wA_maskTab : adrpWordOff 0x90000008#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_31Tab : (adrpWordOff 0x90000008#32 D).getLsbD 31 = true := by
  simp [adrpWordOff]

theorem wA_rdTab : (adrpWordOff 0x90000008#32 D).extractLsb' 0 5 = 8#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_offTab (hlo : ∀ i, i < 12 → D.getLsbD i = false)
    (hhi : ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32) :
    ((adrpWordOff 0x90000008#32 D).extractLsb' 5 19 ++
      (adrpWordOff 0x90000008#32 D).extractLsb' 29 2).signExtend 64 <<< 12 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getMsbD]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm

theorem wC_maskTab : adrWordOff 0x10000008#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_31Tab : (adrWordOff 0x10000008#32 D).getLsbD 31 = false := by
  simp [adrWordOff]

theorem wC_rdTab : (adrWordOff 0x10000008#32 D).extractLsb' 0 5 = 8#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_offTab (hhi : ∀ i, 20 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 20) :
    ((adrWordOff 0x10000008#32 D).extractLsb' 5 19 ++
      (adrWordOff 0x10000008#32 D).extractLsb' 29 2).signExtend 64 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | rfl | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm

theorem wB_maskTab : lo12Word 0 0x91000108#32 D &&& 0x1f800000#32 = 0x11000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wB_bitsTab : (lo12Word 0 0x91000108#32 D).getLsbD 31 = true ∧
    (lo12Word 0 0x91000108#32 D).getLsbD 30 = false ∧
    (lo12Word 0 0x91000108#32 D).getLsbD 29 = false ∧
    (lo12Word 0 0x91000108#32 D).getLsbD 22 = false := by
  simp [lo12Word]

theorem wB_rdTab : (lo12Word 0 0x91000108#32 D).extractLsb' 0 5 = 8#5 ∧
    (lo12Word 0 0x91000108#32 D).extractLsb' 5 5 = 8#5 := by
  constructor <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem wB_immTab : (lo12Word 0 0x91000108#32 D).extractLsb' 10 12 = D.extractLsb' 0 12 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

end words

theorem decode_ATab {P T : BitVec 64} (hr : AdrpInRange P T) :
    decode (adrpWord 0x90000008#32 P T) = some (.adr true (.gpr 8#5) (pageOf T - pageOf P)) := by
  rw [adrpWord, decode_adr_class _ (wA_maskTab _), wA_31Tab, wA_rdTab,
    wA_offTab _ (lo_bits T P) (hi_bits32 _ hr.1 hr.2)]
  rfl

theorem decode_CTab {P T : BitVec 64} (hr : AdrInRange P T) :
    decode (adrWord (adrTemplate 0x91000108#32) P T) = some (.adr false (.gpr 8#5) (T - P)) := by
  rw [adrWord, show adrTemplate 0x91000108#32 = 0x10000008#32 by decide,
    decode_adr_class _ (wC_maskTab _), wC_31Tab, wC_rdTab, if_neg (by decide), wC_offTab _ (hi_bits20 _ hr.1 hr.2)]
  rfl

theorem decode_BTab (T : BitVec 64) :
    decode (lo12Word 0 0x91000108#32 T) =
      some (.addSubImm .W64 .ADD (.gpr 8#5) (.gpr 8#5) (T.extractLsb' 0 12) false) := by
  obtain ⟨b31, b30, b29, b22⟩ := wB_bitsTab T
  rw [decode_addimm_class _ (wB_maskTab _), b31, b30, b29, b22, wB_rdTab T |>.1, wB_rdTab T |>.2, wB_immTab]
  rfl



abbrev symOne : String := "curve25519_dalek:.rodata..Lanon.0"

theorem lookup_One : lookupBlockSym symOne x25519CliMultiLib.blocks = none := by decide

theorem resolve_One (mpl : MultiPlacement) : x25519CliMultiLib.resolve mpl symOne = mpl.ρ symOne := by
  simp [MultiPlacedLib.resolve, lookup_One]

theorem target13 (mpl : MultiPlacement) (o : Nat) (k : RelocKind) (sym : String)
    (hlk : lookup sym x25519CliBlk13.symbols = none) :
    x25519CliBlk13.target (x25519CliMultiLib.blockPlacement mpl 13) { off := o, kind := k, sym := sym } =
      x25519CliMultiLib.resolve mpl sym := by
  simp [CodeBlock.target, CodeBlock.resolve, hlk, addSignedAddr, MultiPlacedLib.blockPlacement]

theorem pw13_64 (mpl : MultiPlacement) :
    x25519CliBlk13.patchedWord (x25519CliMultiLib.blockPlacement mpl 13) 64 =
      if mpl.relax 13 64 then nopWord
      else adrpWord 0x90000008#32 (mpl.base 13 + BitVec.ofNat 64 64) (mpl.ρ symOne) := by
  have hr : x25519CliBlk13.relocAt? 64 = some { off := 64, kind := .adrpHi21, sym := symOne } := by
    decide +kernel
  have h1 : x25519CliBlk13.relaxableAt 64 = true := by decide +kernel
  have hw : x25519CliBlk13.wordAt 64 = 0x90000008#32 := by decide +kernel
  have hlk : lookup symOne x25519CliBlk13.symbols = none := by decide +kernel
  have hrel : (x25519CliMultiLib.blockPlacement mpl 13).relax = mpl.relax 13 := rfl
  have hbase : (x25519CliMultiLib.blockPlacement mpl 13).base = mpl.base 13 := rfl
  have h12 : x25519CliBlk13.relaxableAt 60 = false := by decide +kernel
  have hT := target13 mpl 64 .adrpHi21 symOne hlk
  rw [resolve_One] at hT
  cases h : mpl.relax 13 64 <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h12, hr, hw, hrel, hbase,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, hT,
      patchRelocWord, RelocKind.isGotOrTlsIe]

theorem pw13_68 (mpl : MultiPlacement) :
    x25519CliBlk13.patchedWord (x25519CliMultiLib.blockPlacement mpl 13) 68 =
      if mpl.relax 13 64 then
        adrWord (adrTemplate 0x91000108#32) (mpl.base 13 + BitVec.ofNat 64 68) (mpl.ρ symOne)
      else lo12Word 0 0x91000108#32 (mpl.ρ symOne) := by
  have hr : x25519CliBlk13.relocAt? 68 = some { off := 68, kind := .addLo12, sym := symOne } := by
    decide +kernel
  have h1 : x25519CliBlk13.relaxableAt 64 = true := by decide +kernel
  have h2 : x25519CliBlk13.relaxableAt 68 = false := by decide +kernel
  have hw : x25519CliBlk13.wordAt 68 = 0x91000108#32 := by decide +kernel
  have hlk : lookup symOne x25519CliBlk13.symbols = none := by decide +kernel
  have hrel : (x25519CliMultiLib.blockPlacement mpl 13).relax = mpl.relax 13 := rfl
  have hbase : (x25519CliMultiLib.blockPlacement mpl 13).base = mpl.base 13 := rfl
  have hT := target13 mpl 68 .addLo12 symOne hlk
  rw [resolve_One] at hT
  cases h : mpl.relax 13 64 <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h2, hr, hw, hrel, hbase,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, hT,
      patchRelocWord, RelocKind.isGotOrTlsIe]

theorem placeable13 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) :
    x25519CliBlk13.Placeable (x25519CliMultiLib.blockPlacement mpl 13) := hP.blocks_ok 13 (by decide)

theorem relocTarget13 (mpl : MultiPlacement) (o : Nat) (k : RelocKind) (sym : String)
    (hlk : lookup sym x25519CliBlk13.symbols = none) :
    x25519CliBlk13.relocTarget (x25519CliMultiLib.blockPlacement mpl 13) o { off := o, kind := k, sym := sym } =
      x25519CliMultiLib.resolve mpl sym := by
  have hb2b : x25519CliBlk13.b2bNext? { off := o, kind := k, sym := sym } = none := by
    simp [CodeBlock.b2bNext?, hlk]
  simp only [CodeBlock.relocTarget, hb2b]
  split <;> simp_all [target13]

theorem range13_64 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) :
    AdrpInRange (mpl.base 13 + BitVec.ofNat 64 64) (mpl.ρ symOne) := by
  have hmem : ({ off := 64, kind := .adrpHi21, sym := symOne } : RelocEntry) ∈ x25519CliBlk13.relocs := by
    decide +kernel
  have h := ((placeable13 hP).relocs_ok _ hmem).2.2
  rw [relocTarget13 mpl 64 .adrpHi21 symOne (by decide +kernel), resolve_One] at h
  exact h

theorem range13_68 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hrel : mpl.relax 13 64 = true) :
    AdrInRange (mpl.base 13 + BitVec.ofNat 64 68) (mpl.ρ symOne) := by
  have h1 : x25519CliBlk13.relaxableAt 64 = true := by decide +kernel
  have hr : x25519CliBlk13.relocAt? (64 + 4) = some { off := 68, kind := .addLo12, sym := symOne } := by
    decide +kernel
  have h := (placeable13 hP).relaxed_ok 64 _ (by simp [CodeBlock.relaxedAt, h1]; exact hrel) hr
  rwa [target13 mpl 68 .addLo12 symOne (by decide +kernel), resolve_One] at h

section
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m0) (j : Nat) {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem f13_64 : (bprog mpl j).fetchMem m (mpl.base 13 + BitVec.ofNat 64 64) =
    decode (if mpl.relax 13 64 then nopWord
      else adrpWord 0x90000008#32 (mpl.base 13 + BitVec.ofNat 64 64) (mpl.ρ symOne)) := by
  have hCL' := libCodeLoaded_keepsFrozen hCL hk 13 (by rw [blocks_length]; decide)
  rw [fetch_word hP (by decide) hCL' (by decide) (by rw [blk13, len13]; decide) _ (hook_none mpl j), blk13,
    pw13_64]

theorem f13_68 : (bprog mpl j).fetchMem m (mpl.base 13 + BitVec.ofNat 64 68) =
    decode (if mpl.relax 13 64 then
        adrWord (adrTemplate 0x91000108#32) (mpl.base 13 + BitVec.ofNat 64 68) (mpl.ρ symOne)
      else lo12Word 0 0x91000108#32 (mpl.ρ symOne)) := by
  have hCL' := libCodeLoaded_keepsFrozen hCL hk 13 (by rw [blocks_length]; decide)
  rw [fetch_word hP (by decide) hCL' (by decide) (by rw [blk13, len13]; decide) _ (hook_none mpl j), blk13,
    pw13_68]

end

/-- Offsets 64 and 68 (`adrp x0` / `add x0` of `fe51_mont_a24`, or their relaxed `nop` / `adr`). -/
theorem pair13 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {j : Nat} {s0 : State} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}
    (hk : m0.KeepsFrozen m) (hrun : s0.status = .Running)
    (h : Reach (bprog mpl j) (mkS s0 (mpl.base 13 + BitVec.ofNat 64 72) (upd r 8#5 (mpl.ρ symOne)) sp ps m v) Q) :
    Reach (bprog mpl j) (mkS s0 (mpl.base 13 + BitVec.ofNat 64 64) r sp ps m v) Q := by
  have hf1 := f13_64 hP hCL j hk
  have hf2 := f13_68 hP hCL j hk
  cases hrel : mpl.relax 13 64
  · simp only [hrel, Bool.false_eq_true, if_false] at hf1 hf2
    rw [decode_ATab (range13_64 hP)] at hf1
    rw [decode_BTab] at hf2
    refine Reach.mk hrun hf1 ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel']
    refine Reach.mk hrun hf2 ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel']
    have e1 : (mpl.base 13 + 64#64 &&& 18446744073709547520#64) = pageOf (mpl.base 13 + 64#64) := rfl
    have e2 : ∀ a b : BitVec 64, a + (b - a) = b := by intro a b; bv_omega
    have e3 : upd (upd r 8#5 (pageOf (mpl.ρ symOne))) 8#5 (pageOf (mpl.ρ symOne) +
        BitVec.zeroExtend 64 (BitVec.extractLsb' 0 12 (mpl.ρ symOne))) = upd r 8#5 (mpl.ρ symOne) := by
      funext k; simp only [upd]; split_ifs
      · exact page_add_lo _
      · rfl
    rw [e1, e2, e3]; exact h
  · simp only [hrel, if_true] at hf1 hf2
    rw [decode_nop] at hf1
    rw [decode_CTab (range13_68 hP hrel)] at hf2
    refine Reach.mk hrun hf1 ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel']
    refine Reach.mk hrun hf2 ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel']
    exact h

end X25519Dalek.EMulB
end

section
/-! # Block 13 outside the loops: stores into and loads from word lists, the constant `ONE` -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

section
variable {p : Program} {s0 : State} {pc pc' : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem wcan {a : BitVec 64} {ws : List (BitVec 64)} {Fm : SepProp} (hs : m ⊨ (a ↦₆₄* ws) ∗ Fm)
    (k : Nat) (hk : k < ws.length) : m.canWrite (a + BitVec.ofNat 64 (8 * k)) 8 = true :=
  (sat_words_read hs k hk).2.2

/-- `str x_t, [sp, #off]` into word `k` of the word list in front. -/
theorem x_str_w {t : BitVec 5} {off a : BitVec 64} {ws : List (BitVec 64)} {Fm : SepProp} {k : Nat}
    (ht : t ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .X64 (.gpr t) (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ Fm) (hk : k < ws.length)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* ws.set k (r t)) ∗ Fm) → m.KeepsFrozen m' → Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q :=
  y_str_sp ht hal hA (wcan hs k hk) hpc hrun hf (Reach.wr64 k hs rfl hk h)

/-- `str xzr, [sp, #off]`. -/
theorem x_strz_w {off a : BitVec 64} {ws : List (BitVec 64)} {Fm : SepProp} {k : Nat}
    (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .X64 .xzr (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ Fm) (hk : k < ws.length)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* ws.set k 0#64) ∗ Fm) → m.KeepsFrozen m' → Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q :=
  y_strz_sp hal hA (wcan hs k hk) hpc hrun hf (Reach.wr64 k hs rfl hk h)

/-- `stp x_t1, x_t2, [sp, #off]` into words `k`, `k+1`. -/
theorem x_stp_w {t1 t2 : BitVec 5} {off a : BitVec 64} {ws : List (BitVec 64)} {Fm : SepProp} {k : Nat}
    (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stp .W64 (.gpr t1) (.gpr t2) (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ Fm) (hk : k + 1 < ws.length)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (ws.set k (r t1)).set (k + 1) (r t2)) ∗ Fm) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  exact y_stp_sp ht1 ht2 hal hA (w8' a k) (wcan hs k (by omega)) (wcan hs (k + 1) hk)
    hpc hrun hf (Reach.wr64x2 k hs rfl rfl hk h)

/-- `stp x_t1, x_t2, [sp, #off]!` into words `k`, `k+1`; the new `sp` is word `k`'s address. -/
theorem x_stp_pre_w {t1 t2 : BitVec 5} {off a A : BitVec 64} {ws : List (BitVec 64)} {Fm : SepProp}
    {k : Nat} (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stp .W64 (.gpr t1) (.gpr t2) (.PreIndex .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = A) (hAk : A = a + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ Fm) (hk : k + 1 < ws.length)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (ws.set k (r t1)).set (k + 1) (r t2)) ∗ Fm) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r A ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hAk
  exact y_stp_pre ht1 ht2 hal hA (w8' a k) (wcan hs k (by omega)) (wcan hs (k + 1) hk)
    hpc hrun hf (Reach.wr64x2 k hs rfl rfl hk h)

/-- `stur q_t, [x_b, #off]` into words `k`, `k+1`. -/
theorem x_strq_w {t b : BitVec 5} {off x a lo hi : BitVec 64} {ws : List (BitVec 64)} {Fm : SepProp} {k : Nat}
    (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.strSimd .Q128 t (.UnscaledOffset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ Fm) (hk : k + 1 < ws.length) (ev : v t = hi ++ lo)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (ws.set k lo).set (k + 1) hi) ∗ Fm) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  have c2 := wcan hs (k + 1) hk
  rw [← w8'] at c2
  exact y_strq_u hb (by rw [ex]; exact hA) (w8' a k) (canWrite16 (wcan hs k (by omega)) c2) ev hpc hrun hf
    (Reach.wr64x2 k hs rfl rfl hk h)

/-- `stur q_t, [sp, #off]` into words `k`, `k+1`. -/
theorem x_strq_spw {t : BitVec 5} {off a lo hi : BitVec 64} {ws : List (BitVec 64)} {Fm : SepProp} {k : Nat}
    (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.strSimd .Q128 t (.UnscaledOffset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ Fm) (hk : k + 1 < ws.length) (ev : v t = hi ++ lo)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (ws.set k lo).set (k + 1) hi) ∗ Fm) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  have c2 := wcan hs (k + 1) hk
  rw [← w8'] at c2
  exact y_strq_usp hal hA (w8' a k) (canWrite16 (wcan hs k (by omega)) c2) ev hpc hrun hf
    (Reach.wr64x2 k hs rfl rfl hk h)

/-- `stp q_t1, q_t2, [sp, #off]` into words `k … k+3` of the list in front. -/
theorem x_stpq_w1 {t1 t2 : BitVec 5} {off a lo1 hi1 lo2 hi2 : BitVec 64} {ws : List (BitVec 64)}
    {Fm : SepProp} {k : Nat} (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stpSimd .Q128 t1 t2 (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * k))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ Fm) (hk : k + 3 < ws.length) (ev1 : v t1 = hi1 ++ lo1)
    (ev2 : v t2 = hi2 ++ lo2)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (((ws.set k lo1).set (k + 1) hi1).set (k + 2) lo2).set (k + 3) hi2) ∗ Fm) →
      m.KeepsFrozen m' → Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  have c2 := wcan hs (k + 1) (by omega)
  have c4 := wcan hs (k + 3) hk
  rw [← w8'] at c2
  rw [← w8' a (k + 2)] at c4
  exact y_stpq_sp hal hA (w8' a k) (w16' a k) (w8' a (k + 2)) (canWrite16 (wcan hs k (by omega)) c2)
    (canWrite16 (wcan hs (k + 2) (by omega)) c4) ev1 ev2 hpc hrun hf (Reach.wr64x4 k hs rfl rfl rfl rfl hk h)

end

/-! ## The constant `FieldElement51::ONE` -/

theorem ro_byte {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ᵣ bs) ∗ F) (k j : Nat) (hk : k + j < bs.length) :
    m.read8 (a + BitVec.ofNat 64 k + BitVec.ofNat 64 j) = bs.getD (k + j) 0#8 ∧
      (m.perm (a + BitVec.ofNat 64 k + BitVec.ofNat 64 j)).r = true ∧
      m.isLazyFree (a + BitVec.ofNat 64 k + BitVec.ofNat 64 j) = false := by
  rw [aadd a k j (k + j) rfl]
  have := sat_bytesRO_read hs (k + j) hk
  rw [List.getD_eq_getElem _ _ hk]; exact this

theorem ro_read64 {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ᵣ bs) ∗ F) (k : Nat) (hk : k + 8 ≤ bs.length) :
    m.read64 (a + BitVec.ofNat 64 k) = bs.getD (k + 7) 0#8 ++ bs.getD (k + 6) 0#8 ++ bs.getD (k + 5) 0#8 ++
      bs.getD (k + 4) 0#8 ++ bs.getD (k + 3) 0#8 ++ bs.getD (k + 2) 0#8 ++ bs.getD (k + 1) 0#8 ++
      bs.getD (k + 0) 0#8 ∧ m.canRead (a + BitVec.ofNat 64 k) 8 = true := by
  refine ⟨?_, canRead_of (fun j hj => ⟨(ro_byte hs k j (by omega)).2.1, (ro_byte hs k j (by omega)).2.2⟩)⟩
  have e : ∀ j : Nat, j < 8 → m.read8 (a + BitVec.ofNat 64 k + BitVec.ofNat 64 j) = bs.getD (k + j) 0#8 :=
    fun j hj => (ro_byte hs k j (by omega)).1
  simp only [Memory.read64]
  rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, e 0 (by omega), e 1 (by omega), e 2 (by omega),
    e 3 (by omega), e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega)]

theorem one_read {m : Memory} {a : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦ᵣ fe51OneBytes) ∗ F) (k : Nat)
    (hk : k = 0 ∨ k = 8 ∨ k = 16 ∨ k = 24) :
    m.read64 (a + BitVec.ofNat 64 k) = (if k = 0 then 1#64 else 0#64) ∧
      m.canRead (a + BitVec.ofNat 64 k) 8 = true := by
  have := ro_read64 hs k (by rcases hk with rfl | rfl | rfl | rfl <;> decide)
  refine ⟨?_, this.2⟩
  rw [this.1]; rcases hk with rfl | rfl | rfl | rfl <;> decide

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

theorem addK0 (x : BitVec 64) : x + (0x000#12 : BitVec 12).setWidth 64 = x := by simp

theorem aoff0 (a : BitVec 64) : a = a + BitVec.ofNat 64 (8 * 0) := by simp

theorem list12 {α : Type} (l : List α) (h : l.length = 12) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11, l = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] := by
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, rfl⟩

/-- `ldp q_t1, q_t2, [x_b]` from `FieldElement51::ONE`. -/
theorem x_ldpq_one {p : Program} {s0 : State} {pc pc' : BitVec 64} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}
    {t1 t2 b : BitVec 5} {a : BitVec 64} {F : SepProp} (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldpSimd .Q128 t1 t2 (.Offset (.gpr b) 0x0#64)))
    (hpc : pc + 4#64 = pc') (ex : r b = a) (hs : m ⊨ (a ↦ᵣ fe51OneBytes) ∗ F)
    (h : Reach p (mkS s0 pc' r sp ps m (upd (upd v t1 (0#64 ++ 1#64)) t2 (0#64 ++ 0#64))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  obtain ⟨f0, c0⟩ := one_read hs 0 (by decide)
  obtain ⟨f8, c8⟩ := one_read hs 8 (by decide)
  obtain ⟨f16, c16⟩ := one_read hs 16 (by decide)
  obtain ⟨f24, c24⟩ := one_read hs 24 (by decide)
  simp only [if_true, show ¬ ((8 : Nat) = 0) by decide, show ¬ ((16 : Nat) = 0) by decide,
    show ¬ ((24 : Nat) = 0) by decide, if_false] at f0 f8 f16 f24
  rw [aadd a 0 8 8 rfl |>.symm] at f8 c8
  rw [aadd a 16 8 24 rfl |>.symm] at f24 c24
  exact y_ldpq_o hb (by rw [ex]) (aadd a 0 16 16 rfl) (canRead16 c0 c8) (canRead16 c16 c24)
    f0 f8 f16 f24 hpc hrun hf h

end X25519Dalek.EMulB

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

end X25519Dalek.EMulB
end

section
/-! # Block 13: the 1680-byte stack frame split into the function's buffers and merged back;
the identity accumulator -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

/-- The accumulator the prologue writes: the identity `(0 : 1 : 1 : 0)`. -/
theorem init_ok : fe51Point4Bounded ([0#64, 0#64, 0#64, 0#64, 0#64, 1#64, 0#64, 0#64, 0#64, 0#64, 1#64, 0#64,
      0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64].flatMap unpack64) (2 ^ 52) ∧
    edExtOfBytes ([0#64, 0#64, 0#64, 0#64, 0#64, 1#64, 0#64, 0#64, 0#64, 0#64, 1#64, 0#64,
      0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64].flatMap unpack64) = edExtZero := by
  refine ⟨by unfold fe51Point4Bounded fe51LimbsBoundedAt; decide +kernel, ?_⟩
  unfold edExtOfBytes edExtZero
  congr 1 <;> decide +kernel

end X25519Dalek.EMulB
end

section
/-! # Block 13 outside the loops (generated by tools/gen_main.py A) -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

set_option maxHeartbeats 4000000 in
theorem mainA {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {s0 : State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s0.mem) {S table scalar out : BitVec 64}
    {SC D0 : List (BitVec 8)} {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 : BitVec 64} {G : SepProp} {Q : State → Prop}
    (hrun : s0.status = .Running) (hS : s0.sp = S + 768#64) (hal0 : (s0.sp &&& 15#64) = 0#64)
    (hal : (S &&& 15#64) = 0#64)
    (h0 : s0.regs.regs 0#5 = table) (h1 : s0.regs.regs 1#5 = scalar) (h8 : s0.regs.regs 8#5 = out)
    (hD0 : D0.length = 64) (hSC : SC.length = 32) (hSC31 : (SC.getD 31 0#8).toNat ≤ 127)
    (hm : s0.mem ⊨ ((S + 672#64) ↦₆₄* [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11]) ∗ ((S + 64#64) ↦₆₄* [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19]) ∗ (S ↦ₛ D0) ∗
      (scalar ↦ₛ SC) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ G)
    (hcont : ∀ (sb : State) (r : BitVec 5 → BitVec 64) (ps : PState) (m : Memory) (v : BitVec 5 → BitVec 128),
      sb.status = .Running → s0.mem.KeepsFrozen m →
      r 19#5 = out → r 20#5 = table → r 21#5 = S + 232#64 → r 22#5 = S →
      r 23#5 = BitVec.ofNat 64 (2 * 0) → r 24#5 = S + 392#64 → r 25#5 = 960#64 →
      r 26#5 = s0.regs.regs 26#5 → r 27#5 = s0.regs.regs 27#5 → r 28#5 = s0.regs.regs 28#5 →
      r 29#5 = S + 672#64 → VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved s0.vregs →
      (m ⊨ ((S + 672#64) ↦₆₄* [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 28#5, w3, s0.regs.regs 26#5, s0.regs.regs 25#5, s0.regs.regs 24#5, s0.regs.regs 23#5, s0.regs.regs 22#5, s0.regs.regs 21#5, s0.regs.regs 20#5, s0.regs.regs 19#5]) ∗ ((S + 64#64) ↦₆₄* [0#64, 0#64, 0#64, 0#64, 0#64, 1#64, 0#64, 0#64, 0#64, 0#64, 1#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]) ∗
        (S ↦ₛ scalarRadix16Digits SC) ∗ (scalar ↦ₛ SC) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ G) →
      Reach (bprog mpl 13) (mkS sb (mpl.base 13 + 152#64) r S ps m v) Q) :
    Reach (bprog mpl 13) (mkS s0 (mpl.base 13) s0.regs.regs s0.sp s0.pstate s0.mem s0.vregs.regs) Q := by
  have kf0 : s0.mem.KeepsFrozen s0.mem := Memory.KeepsFrozen.refl _
  have hv0 : VRegFile.calleeSaved ⟨s0.vregs.regs⟩ = VRegFile.calleeSaved s0.vregs := rfl
  have hal672 : ((S + 672#64) &&& 15#64) = 0#64 := aligned_add (by simp [hal]) 672 (by decide)
  -- 0: stp x29, x30, [sp, #-96]!
  refine x_stp_pre_w (t1 := 29#5) (t2 := 30#5) (k := 0) (by decide) (by decide) hal0 hrun (c13_0 hP hCL 13 kf0) rfl (by rw [hS]; exact pcA _ _ _ _ (by decide)) (aoff0 _) hm (by simp) ?_
  intro mw1 hmw1 kw1
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw1
  have kfw1 := kf0.trans kw1
  clear hm kw1
  -- 4: str x28, [sp, #16]
  refine x_str_w (t := 28#5) (k := 2) (by decide) hal672 hrun (c13_4 hP hCL 13 kfw1) (pcA _ _ _ (8#64) (by decide)) rfl hmw1 (by simp) ?_
  intro mw4 hmw4 kw4
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw4
  have kfw4 := kfw1.trans kw4
  clear hmw1 kw4
  -- 8: stp x26, x25, [sp, #32]
  refine x_stp_w (t1 := 26#5) (t2 := 25#5) (k := 4) (by decide) (by decide) hal672 hrun (c13_8 hP hCL 13 kfw4) (pcA _ _ _ (12#64) (by decide)) rfl hmw4 (by simp) ?_
  intro mw8 hmw8 kw8
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw8
  have kfw8 := kfw4.trans kw8
  clear hmw4 kw8
  -- 12: stp x24, x23, [sp, #48]
  refine x_stp_w (t1 := 24#5) (t2 := 23#5) (k := 6) (by decide) (by decide) hal672 hrun (c13_12 hP hCL 13 kfw8) (pcA _ _ _ (16#64) (by decide)) rfl hmw8 (by simp) ?_
  intro mw12 hmw12 kw12
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw12
  have kfw12 := kfw8.trans kw12
  clear hmw8 kw12
  -- 16: stp x22, x21, [sp, #64]
  refine x_stp_w (t1 := 22#5) (t2 := 21#5) (k := 8) (by decide) (by decide) hal672 hrun (c13_16 hP hCL 13 kfw12) (pcA _ _ _ (20#64) (by decide)) rfl hmw12 (by simp) ?_
  intro mw16 hmw16 kw16
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw16
  have kfw16 := kfw12.trans kw16
  clear hmw12 kw16
  -- 20: stp x20, x19, [sp, #80]
  refine x_stp_w (t1 := 20#5) (t2 := 19#5) (k := 10) (by decide) (by decide) hal672 hrun (c13_20 hP hCL 13 kfw16) (pcA _ _ _ (24#64) (by decide)) rfl hmw16 (by simp) ?_
  intro mw20 hmw20 kw20
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw20
  have kfw20 := kfw16.trans kw20
  clear hmw16 kw20
  -- 24: add x29, sp, #0
  refine y_addi_sp (d := 29#5) (by decide) (pcA _ _ _ (28#64) (by decide)) hrun (c13_24 hP hCL 13 kfw20) ?_
  refine Reach.absR (fun r1 hn1 hw1 => ?_)
  have e0_1 : r1 0#5 = table := (hn1 _ (by decide)).trans h0
  have e1_1 : r1 1#5 = scalar := (hn1 _ (by decide)).trans h1
  have e8_1 : r1 8#5 = out := (hn1 _ (by decide)).trans h8
  have e19_1 : r1 19#5 = s0.regs.regs 19#5 := (hn1 _ (by decide)).trans (rfl : s0.regs.regs 19#5 = s0.regs.regs 19#5)
  have e20_1 : r1 20#5 = s0.regs.regs 20#5 := (hn1 _ (by decide)).trans (rfl : s0.regs.regs 20#5 = s0.regs.regs 20#5)
  have e21_1 : r1 21#5 = s0.regs.regs 21#5 := (hn1 _ (by decide)).trans (rfl : s0.regs.regs 21#5 = s0.regs.regs 21#5)
  have e22_1 : r1 22#5 = s0.regs.regs 22#5 := (hn1 _ (by decide)).trans (rfl : s0.regs.regs 22#5 = s0.regs.regs 22#5)
  have e23_1 : r1 23#5 = s0.regs.regs 23#5 := (hn1 _ (by decide)).trans (rfl : s0.regs.regs 23#5 = s0.regs.regs 23#5)
  have e24_1 : r1 24#5 = s0.regs.regs 24#5 := (hn1 _ (by decide)).trans (rfl : s0.regs.regs 24#5 = s0.regs.regs 24#5)
  have e25_1 : r1 25#5 = s0.regs.regs 25#5 := (hn1 _ (by decide)).trans (rfl : s0.regs.regs 25#5 = s0.regs.regs 25#5)
  have e26_1 : r1 26#5 = s0.regs.regs 26#5 := (hn1 _ (by decide)).trans (rfl : s0.regs.regs 26#5 = s0.regs.regs 26#5)
  have e27_1 : r1 27#5 = s0.regs.regs 27#5 := (hn1 _ (by decide)).trans (rfl : s0.regs.regs 27#5 = s0.regs.regs 27#5)
  have e28_1 : r1 28#5 = s0.regs.regs 28#5 := (hn1 _ (by decide)).trans (rfl : s0.regs.regs 28#5 = s0.regs.regs 28#5)
  have e30_1 : r1 30#5 = s0.regs.regs 30#5 := (hn1 _ (by decide)).trans (rfl : s0.regs.regs 30#5 = s0.regs.regs 30#5)
  have e29_1 : r1 29#5 = S + 672#64 := (hw1.trans (addK0 _))
  clear hn1 hw1
  -- 28: sub sp, sp, #672
  refine y_subsp (pcA _ _ _ (32#64) (by decide)) hrun (c13_28 hP hCL 13 kfw20) ?_
  rw [subK2 S 672 _ 0 (by decide), BitVec.add_zero]
  -- 32: mov x20, x0
  refine y_mov (d := 20#5) (b := 0#5) (by decide) (by decide) (pcA _ _ _ (36#64) (by decide)) hrun (c13_32 hP hCL 13 kfw20) ?_
  refine Reach.absR (fun r2 hn2 hw2 => ?_)
  have e0_2 : r2 0#5 = table := (hn2 _ (by decide)).trans e0_1
  have e1_2 : r2 1#5 = scalar := (hn2 _ (by decide)).trans e1_1
  have e8_2 : r2 8#5 = out := (hn2 _ (by decide)).trans e8_1
  have e19_2 : r2 19#5 = s0.regs.regs 19#5 := (hn2 _ (by decide)).trans e19_1
  have e21_2 : r2 21#5 = s0.regs.regs 21#5 := (hn2 _ (by decide)).trans e21_1
  have e22_2 : r2 22#5 = s0.regs.regs 22#5 := (hn2 _ (by decide)).trans e22_1
  have e23_2 : r2 23#5 = s0.regs.regs 23#5 := (hn2 _ (by decide)).trans e23_1
  have e24_2 : r2 24#5 = s0.regs.regs 24#5 := (hn2 _ (by decide)).trans e24_1
  have e25_2 : r2 25#5 = s0.regs.regs 25#5 := (hn2 _ (by decide)).trans e25_1
  have e26_2 : r2 26#5 = s0.regs.regs 26#5 := (hn2 _ (by decide)).trans e26_1
  have e27_2 : r2 27#5 = s0.regs.regs 27#5 := (hn2 _ (by decide)).trans e27_1
  have e28_2 : r2 28#5 = s0.regs.regs 28#5 := (hn2 _ (by decide)).trans e28_1
  have e29_2 : r2 29#5 = S + 672#64 := (hn2 _ (by decide)).trans e29_1
  have e30_2 : r2 30#5 = s0.regs.regs 30#5 := (hn2 _ (by decide)).trans e30_1
  have e20_2 : r2 20#5 = table := (hw2.trans e0_1)
  clear hn2 hw2
  -- 36: add x0, sp, #0
  refine y_addi_sp (d := 0#5) (by decide) (pcA _ _ _ (40#64) (by decide)) hrun (c13_36 hP hCL 13 kfw20) ?_
  refine Reach.absR (fun r3 hn3 hw3 => ?_)
  have e1_3 : r3 1#5 = scalar := (hn3 _ (by decide)).trans e1_2
  have e8_3 : r3 8#5 = out := (hn3 _ (by decide)).trans e8_2
  have e19_3 : r3 19#5 = s0.regs.regs 19#5 := (hn3 _ (by decide)).trans e19_2
  have e20_3 : r3 20#5 = table := (hn3 _ (by decide)).trans e20_2
  have e21_3 : r3 21#5 = s0.regs.regs 21#5 := (hn3 _ (by decide)).trans e21_2
  have e22_3 : r3 22#5 = s0.regs.regs 22#5 := (hn3 _ (by decide)).trans e22_2
  have e23_3 : r3 23#5 = s0.regs.regs 23#5 := (hn3 _ (by decide)).trans e23_2
  have e24_3 : r3 24#5 = s0.regs.regs 24#5 := (hn3 _ (by decide)).trans e24_2
  have e25_3 : r3 25#5 = s0.regs.regs 25#5 := (hn3 _ (by decide)).trans e25_2
  have e26_3 : r3 26#5 = s0.regs.regs 26#5 := (hn3 _ (by decide)).trans e26_2
  have e27_3 : r3 27#5 = s0.regs.regs 27#5 := (hn3 _ (by decide)).trans e27_2
  have e28_3 : r3 28#5 = s0.regs.regs 28#5 := (hn3 _ (by decide)).trans e28_2
  have e29_3 : r3 29#5 = S + 672#64 := (hn3 _ (by decide)).trans e29_2
  have e30_3 : r3 30#5 = s0.regs.regs 30#5 := (hn3 _ (by decide)).trans e30_2
  have e0_3 : r3 0#5 = S := (hw3.trans (addK0 _))
  clear hn3 hw3
  -- 40: mov x19, x8
  refine y_mov (d := 19#5) (b := 8#5) (by decide) (by decide) (pcA _ _ _ (44#64) (by decide)) hrun (c13_40 hP hCL 13 kfw20) ?_
  refine Reach.absR (fun r4 hn4 hw4 => ?_)
  have e0_4 : r4 0#5 = S := (hn4 _ (by decide)).trans e0_3
  have e1_4 : r4 1#5 = scalar := (hn4 _ (by decide)).trans e1_3
  have e8_4 : r4 8#5 = out := (hn4 _ (by decide)).trans e8_3
  have e20_4 : r4 20#5 = table := (hn4 _ (by decide)).trans e20_3
  have e21_4 : r4 21#5 = s0.regs.regs 21#5 := (hn4 _ (by decide)).trans e21_3
  have e22_4 : r4 22#5 = s0.regs.regs 22#5 := (hn4 _ (by decide)).trans e22_3
  have e23_4 : r4 23#5 = s0.regs.regs 23#5 := (hn4 _ (by decide)).trans e23_3
  have e24_4 : r4 24#5 = s0.regs.regs 24#5 := (hn4 _ (by decide)).trans e24_3
  have e25_4 : r4 25#5 = s0.regs.regs 25#5 := (hn4 _ (by decide)).trans e25_3
  have e26_4 : r4 26#5 = s0.regs.regs 26#5 := (hn4 _ (by decide)).trans e26_3
  have e27_4 : r4 27#5 = s0.regs.regs 27#5 := (hn4 _ (by decide)).trans e27_3
  have e28_4 : r4 28#5 = s0.regs.regs 28#5 := (hn4 _ (by decide)).trans e28_3
  have e29_4 : r4 29#5 = S + 672#64 := (hn4 _ (by decide)).trans e29_3
  have e30_4 : r4 30#5 = s0.regs.regs 30#5 := (hn4 _ (by decide)).trans e30_3
  have e19_4 : r4 19#5 = out := (hw4.trans e8_3)
  clear hn4 hw4
  -- 44: add x21, sp, #232
  refine y_addi_sp (d := 21#5) (by decide) (pcA _ _ _ (48#64) (by decide)) hrun (c13_44 hP hCL 13 kfw20) ?_
  refine Reach.absR (fun r5 hn5 hw5 => ?_)
  have e0_5 : r5 0#5 = S := (hn5 _ (by decide)).trans e0_4
  have e1_5 : r5 1#5 = scalar := (hn5 _ (by decide)).trans e1_4
  have e8_5 : r5 8#5 = out := (hn5 _ (by decide)).trans e8_4
  have e19_5 : r5 19#5 = out := (hn5 _ (by decide)).trans e19_4
  have e20_5 : r5 20#5 = table := (hn5 _ (by decide)).trans e20_4
  have e22_5 : r5 22#5 = s0.regs.regs 22#5 := (hn5 _ (by decide)).trans e22_4
  have e23_5 : r5 23#5 = s0.regs.regs 23#5 := (hn5 _ (by decide)).trans e23_4
  have e24_5 : r5 24#5 = s0.regs.regs 24#5 := (hn5 _ (by decide)).trans e24_4
  have e25_5 : r5 25#5 = s0.regs.regs 25#5 := (hn5 _ (by decide)).trans e25_4
  have e26_5 : r5 26#5 = s0.regs.regs 26#5 := (hn5 _ (by decide)).trans e26_4
  have e27_5 : r5 27#5 = s0.regs.regs 27#5 := (hn5 _ (by decide)).trans e27_4
  have e28_5 : r5 28#5 = s0.regs.regs 28#5 := (hn5 _ (by decide)).trans e28_4
  have e29_5 : r5 29#5 = S + 672#64 := (hn5 _ (by decide)).trans e29_4
  have e30_5 : r5 30#5 = s0.regs.regs 30#5 := (hn5 _ (by decide)).trans e30_4
  have e21_5 : r5 21#5 = S + 232#64 := (hw5.trans (addK S _ 232 (by decide)))
  clear hn5 hw5
  -- 48: add x24, sp, #64
  refine y_addi_sp (d := 24#5) (by decide) (pcA _ _ _ (52#64) (by decide)) hrun (c13_48 hP hCL 13 kfw20) ?_
  refine Reach.absR (fun r6 hn6 hw6 => ?_)
  have e0_6 : r6 0#5 = S := (hn6 _ (by decide)).trans e0_5
  have e1_6 : r6 1#5 = scalar := (hn6 _ (by decide)).trans e1_5
  have e8_6 : r6 8#5 = out := (hn6 _ (by decide)).trans e8_5
  have e19_6 : r6 19#5 = out := (hn6 _ (by decide)).trans e19_5
  have e20_6 : r6 20#5 = table := (hn6 _ (by decide)).trans e20_5
  have e21_6 : r6 21#5 = S + 232#64 := (hn6 _ (by decide)).trans e21_5
  have e22_6 : r6 22#5 = s0.regs.regs 22#5 := (hn6 _ (by decide)).trans e22_5
  have e23_6 : r6 23#5 = s0.regs.regs 23#5 := (hn6 _ (by decide)).trans e23_5
  have e25_6 : r6 25#5 = s0.regs.regs 25#5 := (hn6 _ (by decide)).trans e25_5
  have e26_6 : r6 26#5 = s0.regs.regs 26#5 := (hn6 _ (by decide)).trans e26_5
  have e27_6 : r6 27#5 = s0.regs.regs 27#5 := (hn6 _ (by decide)).trans e27_5
  have e28_6 : r6 28#5 = s0.regs.regs 28#5 := (hn6 _ (by decide)).trans e28_5
  have e29_6 : r6 29#5 = S + 672#64 := (hn6 _ (by decide)).trans e29_5
  have e30_6 : r6 30#5 = s0.regs.regs 30#5 := (hn6 _ (by decide)).trans e30_5
  have e24_6 : r6 24#5 = S + 64#64 := (hw6.trans (addK S _ 64 (by decide)))
  clear hn6 hw6
  -- 52: add x22, sp, #0
  refine y_addi_sp (d := 22#5) (by decide) (pcA _ _ _ (56#64) (by decide)) hrun (c13_52 hP hCL 13 kfw20) ?_
  refine Reach.absR (fun r7 hn7 hw7 => ?_)
  have e0_7 : r7 0#5 = S := (hn7 _ (by decide)).trans e0_6
  have e1_7 : r7 1#5 = scalar := (hn7 _ (by decide)).trans e1_6
  have e8_7 : r7 8#5 = out := (hn7 _ (by decide)).trans e8_6
  have e19_7 : r7 19#5 = out := (hn7 _ (by decide)).trans e19_6
  have e20_7 : r7 20#5 = table := (hn7 _ (by decide)).trans e20_6
  have e21_7 : r7 21#5 = S + 232#64 := (hn7 _ (by decide)).trans e21_6
  have e23_7 : r7 23#5 = s0.regs.regs 23#5 := (hn7 _ (by decide)).trans e23_6
  have e24_7 : r7 24#5 = S + 64#64 := (hn7 _ (by decide)).trans e24_6
  have e25_7 : r7 25#5 = s0.regs.regs 25#5 := (hn7 _ (by decide)).trans e25_6
  have e26_7 : r7 26#5 = s0.regs.regs 26#5 := (hn7 _ (by decide)).trans e26_6
  have e27_7 : r7 27#5 = s0.regs.regs 27#5 := (hn7 _ (by decide)).trans e27_6
  have e28_7 : r7 28#5 = s0.regs.regs 28#5 := (hn7 _ (by decide)).trans e28_6
  have e29_7 : r7 29#5 = S + 672#64 := (hn7 _ (by decide)).trans e29_6
  have e30_7 : r7 30#5 = s0.regs.regs 30#5 := (hn7 _ (by decide)).trans e30_6
  have e22_7 : r7 22#5 = S := (hw7.trans (addK0 _))
  clear hn7 hw7
  -- 56: bl
  refine y_bl (add_sub_cancel' _ _) (pcA _ _ _ (60#64) (by decide)) hrun (c13_56 hP hCL 13 kfw20 lk_rad) ?_
  refine Reach.absR (fun r8 hn8 hw8 => ?_)
  have e0_8 : r8 0#5 = S := (hn8 _ (by decide)).trans e0_7
  have e1_8 : r8 1#5 = scalar := (hn8 _ (by decide)).trans e1_7
  have e8_8 : r8 8#5 = out := (hn8 _ (by decide)).trans e8_7
  have e19_8 : r8 19#5 = out := (hn8 _ (by decide)).trans e19_7
  have e20_8 : r8 20#5 = table := (hn8 _ (by decide)).trans e20_7
  have e21_8 : r8 21#5 = S + 232#64 := (hn8 _ (by decide)).trans e21_7
  have e22_8 : r8 22#5 = S := (hn8 _ (by decide)).trans e22_7
  have e23_8 : r8 23#5 = s0.regs.regs 23#5 := (hn8 _ (by decide)).trans e23_7
  have e24_8 : r8 24#5 = S + 64#64 := (hn8 _ (by decide)).trans e24_7
  have e25_8 : r8 25#5 = s0.regs.regs 25#5 := (hn8 _ (by decide)).trans e25_7
  have e26_8 : r8 26#5 = s0.regs.regs 26#5 := (hn8 _ (by decide)).trans e26_7
  have e27_8 : r8 27#5 = s0.regs.regs 27#5 := (hn8 _ (by decide)).trans e27_7
  have e28_8 : r8 28#5 = s0.regs.regs 28#5 := (hn8 _ (by decide)).trans e28_7
  have e29_8 : r8 29#5 = S + 672#64 := (hn8 _ (by decide)).trans e29_7
  have e30_8 : r8 30#5 = mpl.base 13 + 60#64 := hw8
  clear hn8 hw8
  refine call_rad hP rfl hrun hal (libCodeLoaded_keepsFrozen hCL kfw20) e0_8 e1_8 hD0 hSC hSC31 (Satisfies.of_eq hmw20 (Q := (scalar ↦ₛ SC) ∗ (S ↦ₛ D0) ∗ ((S + 672#64) ↦₆₄* [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 28#5, w3, s0.regs.regs 26#5, s0.regs.regs 25#5, s0.regs.regs 24#5, s0.regs.regs 23#5, s0.regs.regs 22#5, s0.regs.regs 21#5, s0.regs.regs 20#5, s0.regs.regs 19#5]) ∗ ((S + 64#64) ↦₆₄* [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19]) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ G)) ?_
  intro sf1 hrun1 hsp1 hcs1 hv1 hm1 hkf1
  rw [e30_8]
  have e19_c1 : sf1.regs.regs 19#5 = out := (hcs1.1).trans e19_8
  have e20_c1 : sf1.regs.regs 20#5 = table := (hcs1.2.1).trans e20_8
  have e21_c1 : sf1.regs.regs 21#5 = S + 232#64 := (hcs1.2.2.1).trans e21_8
  have e22_c1 : sf1.regs.regs 22#5 = S := (hcs1.2.2.2.1).trans e22_8
  have e23_c1 : sf1.regs.regs 23#5 = s0.regs.regs 23#5 := (hcs1.2.2.2.2.1).trans e23_8
  have e24_c1 : sf1.regs.regs 24#5 = S + 64#64 := (hcs1.2.2.2.2.2.1).trans e24_8
  have e25_c1 : sf1.regs.regs 25#5 = s0.regs.regs 25#5 := (hcs1.2.2.2.2.2.2.1).trans e25_8
  have e26_c1 : sf1.regs.regs 26#5 = s0.regs.regs 26#5 := (hcs1.2.2.2.2.2.2.2.1).trans e26_8
  have e27_c1 : sf1.regs.regs 27#5 = s0.regs.regs 27#5 := (hcs1.2.2.2.2.2.2.2.2.1).trans e27_8
  have e28_c1 : sf1.regs.regs 28#5 = s0.regs.regs 28#5 := (hcs1.2.2.2.2.2.2.2.2.2.1).trans e28_8
  have e29_c1 : sf1.regs.regs 29#5 = S + 672#64 := (hcs1.2.2.2.2.2.2.2.2.2.2).trans e29_8
  have kfc1 : s0.mem.KeepsFrozen sf1.mem := kfw20.trans hkf1
  have hvc1 : VRegFile.calleeSaved ⟨sf1.vregs.regs⟩ = VRegFile.calleeSaved s0.vregs := hv1.trans hv0
  clear hcs1 hkf1 hv1
  -- 60: movi v0.2d, #0
  refine y_movi0 (pcA _ _ _ (64#64) (by decide)) hrun1 (c13_60 hP hCL 13 kfc1) ?_
  have hvm := cs_upd (i := 0#5) (x := 0#128) (by decide) hvc1
  -- 64, 68: adrp/add x8, FieldElement51::ONE
  refine pair13 hP hCL (j := 13) kfc1 hrun1 ?_
  refine Reach.absR (fun r9 hn9 hw9 => ?_)
  have e19_9 : r9 19#5 = out := (hn9 _ (by decide)).trans e19_c1
  have e20_9 : r9 20#5 = table := (hn9 _ (by decide)).trans e20_c1
  have e21_9 : r9 21#5 = S + 232#64 := (hn9 _ (by decide)).trans e21_c1
  have e22_9 : r9 22#5 = S := (hn9 _ (by decide)).trans e22_c1
  have e23_9 : r9 23#5 = s0.regs.regs 23#5 := (hn9 _ (by decide)).trans e23_c1
  have e24_9 : r9 24#5 = S + 64#64 := (hn9 _ (by decide)).trans e24_c1
  have e25_9 : r9 25#5 = s0.regs.regs 25#5 := (hn9 _ (by decide)).trans e25_c1
  have e26_9 : r9 26#5 = s0.regs.regs 26#5 := (hn9 _ (by decide)).trans e26_c1
  have e27_9 : r9 27#5 = s0.regs.regs 27#5 := (hn9 _ (by decide)).trans e27_c1
  have e28_9 : r9 28#5 = s0.regs.regs 28#5 := (hn9 _ (by decide)).trans e28_c1
  have e29_9 : r9 29#5 = S + 672#64 := (hn9 _ (by decide)).trans e29_c1
  have e8_9 : r9 8#5 = fe51_one mpl := hw9
  clear hn9 hw9
  -- 72: ldp q1, q2, [x8]
  refine x_ldpq_one (t1 := 1#5) (t2 := 2#5) (by decide) hrun1 (c13_72 hP hCL 13 kfc1) (pcA _ _ _ (76#64) (by decide)) e8_9 (Satisfies.of_eq hm1 (Q := (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ ((S + 64#64) ↦₆₄* [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19]) ∗ ((S + 672#64) ↦₆₄* [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 28#5, w3, s0.regs.regs 26#5, s0.regs.regs 25#5, s0.regs.regs 24#5, s0.regs.regs 23#5, s0.regs.regs 22#5, s0.regs.regs 21#5, s0.regs.regs 20#5, s0.regs.regs 19#5]) ∗ (S ↦ₛ scalarRadix16Digits SC) ∗ (scalar ↦ₛ SC) ∗ G)) ?_
  have hvq := cs_upd (i := 2#5) (x := 0#64 ++ 0#64) (by decide) (cs_upd (i := 1#5) (x := 0#64 ++ 1#64) (by decide) hvm)
  -- 76: mov x23, xzr
  refine y_movzr (d := 23#5) (by decide) (pcA _ _ _ (80#64) (by decide)) hrun1 (c13_76 hP hCL 13 kfc1) ?_
  refine Reach.absR (fun r10 hn10 hw10 => ?_)
  have e8_10 : r10 8#5 = fe51_one mpl := (hn10 _ (by decide)).trans e8_9
  have e19_10 : r10 19#5 = out := (hn10 _ (by decide)).trans e19_9
  have e20_10 : r10 20#5 = table := (hn10 _ (by decide)).trans e20_9
  have e21_10 : r10 21#5 = S + 232#64 := (hn10 _ (by decide)).trans e21_9
  have e22_10 : r10 22#5 = S := (hn10 _ (by decide)).trans e22_9
  have e24_10 : r10 24#5 = S + 64#64 := (hn10 _ (by decide)).trans e24_9
  have e25_10 : r10 25#5 = s0.regs.regs 25#5 := (hn10 _ (by decide)).trans e25_9
  have e26_10 : r10 26#5 = s0.regs.regs 26#5 := (hn10 _ (by decide)).trans e26_9
  have e27_10 : r10 27#5 = s0.regs.regs 27#5 := (hn10 _ (by decide)).trans e27_9
  have e28_10 : r10 28#5 = s0.regs.regs 28#5 := (hn10 _ (by decide)).trans e28_9
  have e29_10 : r10 29#5 = S + 672#64 := (hn10 _ (by decide)).trans e29_9
  have e23_10 : r10 23#5 = BitVec.ofNat 64 (2 * 0) := hw10
  clear hn10 hw10
  -- 80: mov w25, #960
  refine y_movz32 (d := 25#5) (by decide) (pcA _ _ _ (84#64) (by decide)) hrun1 (c13_80 hP hCL 13 kfc1) ?_
  refine Reach.absR (fun r11 hn11 hw11 => ?_)
  have e8_11 : r11 8#5 = fe51_one mpl := (hn11 _ (by decide)).trans e8_10
  have e19_11 : r11 19#5 = out := (hn11 _ (by decide)).trans e19_10
  have e20_11 : r11 20#5 = table := (hn11 _ (by decide)).trans e20_10
  have e21_11 : r11 21#5 = S + 232#64 := (hn11 _ (by decide)).trans e21_10
  have e22_11 : r11 22#5 = S := (hn11 _ (by decide)).trans e22_10
  have e23_11 : r11 23#5 = BitVec.ofNat 64 (2 * 0) := (hn11 _ (by decide)).trans e23_10
  have e24_11 : r11 24#5 = S + 64#64 := (hn11 _ (by decide)).trans e24_10
  have e26_11 : r11 26#5 = s0.regs.regs 26#5 := (hn11 _ (by decide)).trans e26_10
  have e27_11 : r11 27#5 = s0.regs.regs 27#5 := (hn11 _ (by decide)).trans e27_10
  have e28_11 : r11 28#5 = s0.regs.regs 28#5 := (hn11 _ (by decide)).trans e28_10
  have e29_11 : r11 29#5 = S + 672#64 := (hn11 _ (by decide)).trans e29_10
  have e25_11 : r11 25#5 = 960#64 := (by rw [hw11]; rfl)
  clear hn11 hw11
  have hmA : sf1.mem ⊨ ((S + 64#64) ↦₆₄* [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19]) ∗ (((S + 672#64) ↦₆₄* [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 28#5, w3, s0.regs.regs 26#5, s0.regs.regs 25#5, s0.regs.regs 24#5, s0.regs.regs 23#5, s0.regs.regs 22#5, s0.regs.regs 21#5, s0.regs.regs 20#5, s0.regs.regs 19#5]) ∗ (S ↦ₛ scalarRadix16Digits SC) ∗ (scalar ↦ₛ SC) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ G) := Satisfies.of_eq hm1
  -- 84: strz
  refine x_strz_w (k := 4) hal hrun1 (c13_84 hP hCL 13 kfc1) (pcA _ _ _ (88#64) (by decide)) (aadd S 64 (8 * 4) 96 rfl).symm hmA (by simp) ?_
  intro mw84 hmw84 kw84
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw84
  have kfw84 := kfc1.trans kw84
  clear hmA kw84
  -- 88: strz
  refine x_strz_w (k := 9) hal hrun1 (c13_88 hP hCL 13 kfw84) (pcA _ _ _ (92#64) (by decide)) (aadd S 64 (8 * 9) 136 rfl).symm hmw84 (by simp) ?_
  intro mw88 hmw88 kw88
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw88
  have kfw88 := kfw84.trans kw88
  clear hmw84 kw88
  -- 92: strq24
  refine x_strq_w (t := 0#5) (k := 15) (lo := 0#64) (hi := 0#64) (by decide) hrun1 (c13_92 hP hCL 13 kfw88) (pcA _ _ _ (96#64) (by decide)) e24_11 rfl hmw88 (by simp) (by simp) ?_
  intro mw92 hmw92 kw92
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw92
  have kfw92 := kfw88.trans kw92
  clear hmw88 kw92
  -- 96: strq24
  refine x_strq_w (t := 0#5) (k := 17) (lo := 0#64) (hi := 0#64) (by decide) hrun1 (c13_96 hP hCL 13 kfw92) (pcA _ _ _ (100#64) (by decide)) e24_11 rfl hmw92 (by simp) (by simp) ?_
  intro mw96 hmw96 kw96
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw96
  have kfw96 := kfw92.trans kw96
  clear hmw92 kw96
  -- 100: add x24, sp, #392
  refine y_addi_sp (d := 24#5) (by decide) (pcA _ _ _ (104#64) (by decide)) hrun1 (c13_100 hP hCL 13 kfw96) ?_
  refine Reach.absR (fun r12 hn12 hw12 => ?_)
  have e8_12 : r12 8#5 = fe51_one mpl := (hn12 _ (by decide)).trans e8_11
  have e19_12 : r12 19#5 = out := (hn12 _ (by decide)).trans e19_11
  have e20_12 : r12 20#5 = table := (hn12 _ (by decide)).trans e20_11
  have e21_12 : r12 21#5 = S + 232#64 := (hn12 _ (by decide)).trans e21_11
  have e22_12 : r12 22#5 = S := (hn12 _ (by decide)).trans e22_11
  have e23_12 : r12 23#5 = BitVec.ofNat 64 (2 * 0) := (hn12 _ (by decide)).trans e23_11
  have e25_12 : r12 25#5 = 960#64 := (hn12 _ (by decide)).trans e25_11
  have e26_12 : r12 26#5 = s0.regs.regs 26#5 := (hn12 _ (by decide)).trans e26_11
  have e27_12 : r12 27#5 = s0.regs.regs 27#5 := (hn12 _ (by decide)).trans e27_11
  have e28_12 : r12 28#5 = s0.regs.regs 28#5 := (hn12 _ (by decide)).trans e28_11
  have e29_12 : r12 29#5 = S + 672#64 := (hn12 _ (by decide)).trans e29_11
  have e24_12 : r12 24#5 = S + 392#64 := (hw12.trans (addK S _ 392 (by decide)))
  clear hn12 hw12
  -- 104: strqsp
  refine x_strq_spw (t := 1#5) (k := 5) (lo := 1#64) (hi := 0#64) hal hrun1 (c13_104 hP hCL 13 kfw96) (pcA _ _ _ (108#64) (by decide)) (aadd S 64 (8 * 5) 104 rfl).symm hmw96 (by simp) (by simp) ?_
  intro mw104 hmw104 kw104
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw104
  have kfw104 := kfw96.trans kw104
  clear hmw96 kw104
  -- 108: stpq
  refine x_stpq_w1 (t1 := 0#5) (t2 := 0#5) (k := 0) (lo1 := 0#64) (hi1 := 0#64) (lo2 := 0#64) (hi2 := 0#64) hal hrun1 (c13_108 hP hCL 13 kfw104) (pcA _ _ _ (112#64) (by decide)) (aadd S 64 (8 * 0) 64 rfl).symm hmw104 (by simp) (by simp) (by simp) ?_
  intro mw108 hmw108 kw108
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw108
  have kfw108 := kfw104.trans kw108
  clear hmw104 kw108
  -- 112: strqsp
  refine x_strq_spw (t := 2#5) (k := 7) (lo := 0#64) (hi := 0#64) hal hrun1 (c13_112 hP hCL 13 kfw108) (pcA _ _ _ (116#64) (by decide)) (aadd S 64 (8 * 7) 120 rfl).symm hmw108 (by simp) (by simp) ?_
  intro mw112 hmw112 kw112
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw112
  have kfw112 := kfw108.trans kw112
  clear hmw108 kw112
  -- 116: strz
  refine x_strz_w (k := 14) hal hrun1 (c13_116 hP hCL 13 kfw112) (pcA _ _ _ (120#64) (by decide)) (aadd S 64 (8 * 14) 176 rfl).symm hmw112 (by simp) ?_
  intro mw116 hmw116 kw116
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw116
  have kfw116 := kfw112.trans kw116
  clear hmw112 kw116
  -- 120: stpq
  refine x_stpq_w1 (t1 := 1#5) (t2 := 2#5) (k := 10) (lo1 := 1#64) (hi1 := 0#64) (lo2 := 0#64) (hi2 := 0#64) hal hrun1 (c13_120 hP hCL 13 kfw116) (pcA _ _ _ (124#64) (by decide)) (aadd S 64 (8 * 10) 144 rfl).symm hmw116 (by simp) (by simp) (by simp) ?_
  intro mw120 hmw120 kw120
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw120
  have kfw120 := kfw116.trans kw120
  clear hmw116 kw120
  -- 124: strz
  refine x_strz_w (k := 19) hal hrun1 (c13_124 hP hCL 13 kfw120) (pcA _ _ _ (128#64) (by decide)) (aadd S 64 (8 * 19) 216 rfl).symm hmw120 (by simp) ?_
  intro mw124 hmw124 kw124
  simp only [List.set_cons_succ, List.set_cons_zero] at hmw124
  have kfw124 := kfw120.trans kw124
  clear hmw120 kw124
  -- 128: cmp x23, #64; 132: b.ne 152
  refine y_cmpi (n := 23#5) (by decide) (pcA _ _ _ (132#64) (by decide)) hrun1 (c13_128 hP hCL 13 kfw124) ?_
  refine y_bcond_t (by rw [e23_12]; decide) (pcA _ _ _ (152#64) (by decide)) hrun1 (c13_132 hP hCL 13 kfw124) ?_
  exact hcont _ _ _ _ _ hrun1 kfw124 e19_12 e20_12 e21_12 e22_12 e23_12 e24_12 e25_12 e26_12 e27_12 e28_12 e29_12 hvq (Satisfies.of_eq hmw124)

end X25519Dalek.EMulB
end

section
/-! # Block 13: the prologue (offsets 0-148) as a `Steps` statement -/

set_option autoImplicit false

namespace X25519Dalek.EMulB

open Arm64 Arm64.Obj

set_option maxHeartbeats 4000000 in
theorem basepointTable_mul_base_prologue_dev {mpl : Arm64.Obj.MultiPlacement}
    (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S table scalar out : BitVec 64}
    {scalar_bs : List (BitVec 8)} {G : Arm64.SepProp}
    (hrun : s.status = .Running) (hpc : s.pc = mpl.base 13) (hsp : s.sp = S + 768#64)
    (hal : (S &&& 15#64) = 0#64)
    (h0 : s.regs.regs 0#5 = table) (h1 : s.regs.regs 1#5 = scalar) (h8 : s.regs.regs 8#5 = out)
    (hsc : scalar_bs.length = 32) (hsc31 : (scalar_bs.getD 31 0#8).toNat ≤ 127)
    (hs : s.mem ⊨ Arm64.memRegion (S + 672#64) 96 ∗ Arm64.memRegion (S + 64#64) 160 ∗ Arm64.memRegion S 64 ∗
      (scalar ↦ₛ scalar_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ G) :
    ∃ s' : Arm64.State, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 13) s s' ∧
      s'.status = .Running ∧ s'.pc = mpl.base 13 + 152#64 ∧ s'.sp = S ∧
      s'.regs.regs 19#5 = out ∧ s'.regs.regs 20#5 = table ∧ s'.regs.regs 21#5 = S + 232#64 ∧
      s'.regs.regs 22#5 = S ∧ s'.regs.regs 23#5 = 0#64 ∧ s'.regs.regs 24#5 = S + 392#64 ∧
      s'.regs.regs 25#5 = 960#64 ∧ s'.regs.regs 26#5 = s.regs.regs 26#5 ∧
      s'.regs.regs 27#5 = s.regs.regs 27#5 ∧ s'.regs.regs 28#5 = s.regs.regs 28#5 ∧
      s'.regs.regs 29#5 = S + 672#64 ∧
      Arm64.VRegFile.calleeSaved s'.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      ∃ (w3 : BitVec 64) (acc : List (BitVec 8)),
        (s'.mem ⊨ ((S + 672#64) ↦₆₄* [s.regs.regs 29#5, s.regs.regs 30#5, s.regs.regs 28#5, w3, s.regs.regs 26#5, s.regs.regs 25#5, s.regs.regs 24#5, s.regs.regs 23#5, s.regs.regs 22#5, s.regs.regs 21#5, s.regs.regs 20#5, s.regs.regs 19#5]) ∗ ((S + 64#64) ↦ₛ acc) ∗
          (S ↦ₛ scalarRadix16Digits scalar_bs) ∗ (scalar ↦ₛ scalar_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ G) ∧
        fe51Point4Bounded acc (2 ^ 52) ∧ edExtOfBytes acc = edExtZero := by
  have hal0 : (s.sp &&& 15#64) = 0#64 := by rw [hsp]; exact aligned_add (by simp [hal]) 768 (by decide)
  obtain ⟨W, hW, hs1⟩ := memRegion_words' (S + 672#64) 12 (by norm_num) hs
  have hs2 : s.mem ⊨ memRegion (S + 64#64) (8 * 20) ∗ (((S + 672#64) ↦₆₄* W) ∗ memRegion S 64 ∗
      (scalar ↦ₛ scalar_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ G) := Satisfies.of_eq hs1
  obtain ⟨Aw, hAw, hs3⟩ := memRegion_words' (S + 64#64) 20 (by norm_num) hs2
  have hs4 : s.mem ⊨ memRegion S 64 ∗ (((S + 64#64) ↦₆₄* Aw) ∗ ((S + 672#64) ↦₆₄* W) ∗
      (scalar ↦ₛ scalar_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ G) := Satisfies.of_eq hs3
  obtain ⟨D0, hD0, hs5⟩ := memRegion_bytes S 64 (by norm_num) hs4
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, rfl⟩ := list12 W hW
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, rfl⟩ := list20 Aw hAw
  have hR := mainA (Q := fun s' => s'.status = .Running ∧ s'.pc = mpl.base 13 + 152#64 ∧ s'.sp = S ∧
      s'.regs.regs 19#5 = out ∧ s'.regs.regs 20#5 = table ∧ s'.regs.regs 21#5 = S + 232#64 ∧
      s'.regs.regs 22#5 = S ∧ s'.regs.regs 23#5 = 0#64 ∧ s'.regs.regs 24#5 = S + 392#64 ∧
      s'.regs.regs 25#5 = 960#64 ∧ s'.regs.regs 26#5 = s.regs.regs 26#5 ∧
      s'.regs.regs 27#5 = s.regs.regs 27#5 ∧ s'.regs.regs 28#5 = s.regs.regs 28#5 ∧
      s'.regs.regs 29#5 = S + 672#64 ∧
      VRegFile.calleeSaved s'.vregs = VRegFile.calleeSaved s.vregs ∧
      ∃ (w3 : BitVec 64) (acc : List (BitVec 8)),
        (s'.mem ⊨ ((S + 672#64) ↦₆₄* [s.regs.regs 29#5, s.regs.regs 30#5, s.regs.regs 28#5, w3, s.regs.regs 26#5, s.regs.regs 25#5, s.regs.regs 24#5, s.regs.regs 23#5, s.regs.regs 22#5, s.regs.regs 21#5, s.regs.regs 20#5, s.regs.regs 19#5]) ∗ ((S + 64#64) ↦ₛ acc) ∗
          (S ↦ₛ scalarRadix16Digits scalar_bs) ∗ (scalar ↦ₛ scalar_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ G) ∧
        fe51Point4Bounded acc (2 ^ 52) ∧ edExtOfBytes acc = edExtZero)
    hP hCL hrun hsp hal0 hal h0 h1 h8 hD0 hsc hsc31 (Satisfies.of_eq hs5)
    (fun sb r ps m v hrunA kfA e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 hvA hmA => by
      rw [words_eq_bytes (S + 64#64)] at hmA
      exact Reach.done ⟨hrunA, rfl, rfl, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, hvA, w3, _,
        Satisfies.of_eq hmA, init_ok.1, init_ok.2⟩)
  have e : mkS s (mpl.base 13) s.regs.regs s.sp s.pstate s.mem s.vregs.regs = s := by rw [← hpc]; rfl
  rw [e] at hR
  exact hR

end X25519Dalek.EMulB
end

section
open X25519Dalek

theorem solution {mpl : Arm64.Obj.MultiPlacement}
    (hP : x25519CliMultiLib.Placeable mpl) {s : Arm64.State}
    (hCL : x25519CliMultiLib.CodeLoaded mpl s.mem) {S table scalar out : BitVec 64}
    {scalar_bs : List (BitVec 8)} {G : Arm64.SepProp}
    (hrun : s.status = .Running) (hpc : s.pc = mpl.base 13) (hsp : s.sp = S + 768#64)
    (hal : (S &&& 15#64) = 0#64)
    (h0 : s.regs.regs 0#5 = table) (h1 : s.regs.regs 1#5 = scalar) (h8 : s.regs.regs 8#5 = out)
    (hsc : scalar_bs.length = 32) (hsc31 : (scalar_bs.getD 31 0#8).toNat ≤ 127)
    (hs : s.mem ⊨ Arm64.memRegion (S + 672#64) 96 ∗ Arm64.memRegion (S + 64#64) 160 ∗ Arm64.memRegion S 64 ∗
      (scalar ↦ₛ scalar_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ G) :
    ∃ s' : Arm64.State, Arm64.Steps (x25519CliMultiLib.blockProgram mpl 13) s s' ∧
      s'.status = .Running ∧ s'.pc = mpl.base 13 + 152#64 ∧ s'.sp = S ∧
      s'.regs.regs 19#5 = out ∧ s'.regs.regs 20#5 = table ∧ s'.regs.regs 21#5 = S + 232#64 ∧
      s'.regs.regs 22#5 = S ∧ s'.regs.regs 23#5 = 0#64 ∧ s'.regs.regs 24#5 = S + 392#64 ∧
      s'.regs.regs 25#5 = 960#64 ∧ s'.regs.regs 26#5 = s.regs.regs 26#5 ∧
      s'.regs.regs 27#5 = s.regs.regs 27#5 ∧ s'.regs.regs 28#5 = s.regs.regs 28#5 ∧
      s'.regs.regs 29#5 = S + 672#64 ∧
      Arm64.VRegFile.calleeSaved s'.vregs = Arm64.VRegFile.calleeSaved s.vregs ∧
      ∃ (w3 : BitVec 64) (acc : List (BitVec 8)),
        (s'.mem ⊨ ((S + 672#64) ↦₆₄* [s.regs.regs 29#5, s.regs.regs 30#5, s.regs.regs 28#5, w3, s.regs.regs 26#5, s.regs.regs 25#5, s.regs.regs 24#5, s.regs.regs 23#5, s.regs.regs 22#5, s.regs.regs 21#5, s.regs.regs 20#5, s.regs.regs 19#5]) ∗ ((S + 64#64) ↦ₛ acc) ∗
          (S ↦ₛ scalarRadix16Digits scalar_bs) ∗ (scalar ↦ₛ scalar_bs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ G) ∧
        fe51Point4Bounded acc (2 ^ 52) ∧ edExtOfBytes acc = edExtZero :=
  X25519Dalek.EMulB.basepointTable_mul_base_prologue_dev hP hCL hrun hpc hsp hal h0 h1 h8 hsc hsc31 hs

end
