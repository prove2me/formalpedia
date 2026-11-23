-- Prove2me | solution 1 for X25519Dalek.fnOk_montgomeryPoint_mul_v2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-23T21:24:30.707+00:00
-- url     : https://prove2.me/submissions/56bc31b9-fb4d-48ba-aab7-0e7e2812e5ae

import Definitions.Def_X25519Dalek_PlacedObj
import Definitions.Def_X25519Dalek_Rfc7748
import Definitions.Def_X25519Dalek_Spec
import Theorems.Thm_X25519Dalek_steps_keepsFrozen_v2
import Theorems.Thm_X25519Dalek_fnOk_black_box_v2
import Theorems.Thm_X25519Dalek_fnOk_bits_le_rev_nth_one_v2
import Theorems.Thm_X25519Dalek_fnOk_differential_add_and_double_v2
import Theorems.Thm_X25519Dalek_fnOk_projectivePoint_as_affine_v2
import Mathlib.Data.BitVec
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

section
section
/-! # Separation-logic heap algebra

Ported from google-deepmind/code-verification @ 8c8d371f (Apache-2.0),
`arm64-semantics/ProofLib/CoreLemmas.lean` and `ProofLib/SepLogic/Model.lean`: the plain lemmas
about `Heap.Disjoint`, `Heap.union`, `Heap.Matches` and `sepConj`, with ProofLib's custom simp
attributes removed. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

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

theorem pointsToBytes_split (a : BitVec 64) (bs : List (BitVec 8)) (n : Nat) (hn : n ≤ bs.length) :
    (a ↦ₛ bs) = (a ↦ₛ bs.take n) ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bs.drop n) := by
  have h := pointsToBytes_append a (bs.take n) (bs.drop n)
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
end

section
section
/-! # Instruction fetch in the placed x25519 library, and execution by backward chaining

`Step` does not depend on which block's program runs it when no hooks are installed, so a callee's
contract (stated for its own block) is usable from the caller's block. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

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
  interval_cases i <;> simp

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

end X25519Dalek.LP

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

namespace X25519Dalek.LP

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

/-- Register reads of the entry state, as `mkS` sees them. -/
theorem readGpr_eq (s : State) (i : BitVec 5) (h : i ≠ 31#5) :
    s.readReg64 (.gpr i) = s.regs.regs i := by
  simp [State.readReg64, RegFile.read, h]

end X25519Dalek.LP

end
end

section
section
/-! # Code stays loaded; stepping on abstract states; small stack frames -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

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

theorem unpack64_pack64 (l : List (BitVec 8)) (h : l.length = 8) : unpack64 (pack64 l) = l := by
  match l, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    simp only [pack64, unpack64, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq,
      and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
      interval_cases i <;> simp

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

/-- Focus-free consequences of owning one 64-bit cell at the head. -/
theorem cell_write {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F)
    (w : BitVec 64) :
    m.canWrite a 8 = true ∧ m.KeepsFrozen (m.write64 a w) ∧ (m.write64 a w ⊨ (a ↦₆₄ w) ∗ F) := by
  have h := sat64_read hs
  exact ⟨h.2.2, keepsFrozen_write64_of_rw (fun i hi => (sat64_byte hs i hi).2.1) w, sat64_write hs w⟩

end X25519Dalek.LP

end
end

section
section
/-! # Arithmetic facts for the instruction evaluators and byte encodings -/

set_option autoImplicit false

namespace X25519Dalek.LP

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

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem and15_toNat (x : BitVec 64) : (x &&& 15#64).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and]
  have : (15#64 : BitVec 64).toNat = 2 ^ 4 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-- Alignment of `sp - k` for `k` a multiple of 16, from alignment of `sp`. -/
theorem aligned_sub {x : BitVec 64} (h : (x &&& 15#64 == 0#64) = true) (k : Nat) (hk : k % 16 = 0)
    (hk' : k < 2 ^ 64) : (x - BitVec.ofNat 64 k &&& 15#64) = 0#64 := by
  have h0 : x &&& 15#64 = 0#64 := by simpa using h
  have h1 := congrArg BitVec.toNat h0
  rw [and15_toNat] at h1
  apply BitVec.eq_of_toNat_eq
  rw [and15_toNat]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_zero] at h1 ⊢
  rw [Nat.mod_eq_of_lt hk'] 
  omega

end X25519Dalek.LP

end
end

section
section
/-! # Relocated `BL` words and calls to other blocks -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

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
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  interval_cases i <;> (try simp only [decide_eq_decide]) <;> (try split at h1) <;> omega

theorem lo_bits2 (D : BitVec 64) (h : D.toNat % 4 = 0) : ∀ i, i < 2 → D.getLsbD i = false := by
  intro i hi
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  generalize D.toNat = n at h ⊢
  interval_cases i <;> simp <;> omega

theorem bw_mask (D : BitVec 64) :
    ((0x94000000#32 &&& 0xfc000000#32) ||| ((D >>> 2).setWidth 32 &&& 0x03ffffff#32)) &&&
      0xfc000000#32 = 0x94000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  interval_cases i <;> simp

theorem bw_off (D : BitVec 64) (hlo : ∀ i, i < 2 → D.getLsbD i = false)
    (hhi : ∀ i, 27 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 27) :
    ((((0x94000000#32 &&& 0xfc000000#32) ||| ((D >>> 2).setWidth 32 &&& 0x03ffffff#32))).extractLsb' 0 26).signExtend 64 <<< 2 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.msb, BitVec.getMsbD]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | exact (hlo _ (by omega)).symm | exact hlo _ (by omega) | rfl |
      exact (hhi _ (by omega) (by omega)).symm | exact hhi _ (by omega) (by omega)

/-- A relocated `bl` decodes to a branch-with-link whose offset reaches the target, when the
target is in range. -/
theorem decode_branchWord (place target : BitVec 64) (h : BranchInRange place target) :
    decode (branchWord 0x94000000#32 place target) = some (.bl (target - place)) := by
  unfold branchWord
  rw [decode_bl_class _ (bw_mask _)]
  congr 2
  exact bw_off _ (lo_bits2 _ h.1) (hi_bits27 _ h.2.1 h.2.2)

end X25519Dalek.LP

namespace X25519Dalek.LP

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

end X25519Dalek.LP

namespace X25519Dalek.LP

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

end X25519Dalek.LP

end
end

section
section
/-! # Stack frames as lists of 64-bit words

`a ↦₆₄* ws` owns the words `ws` at `a, a + 8, …`; indexed reads and writes; conversions to and
from byte slices and `memRegion`. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

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

theorem flatMap_unpack64_length (ws : List (BitVec 64)) :
    (ws.flatMap unpack64).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [List.flatMap_cons, ih]; omega

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

end X25519Dalek.LP

namespace X25519Dalek.LP
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

theorem sat_bytes_access {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ₛ bs) ∗ F) (k n : Nat) (h : k + n ≤ bs.length) :
    m.canRead (a + BitVec.ofNat 64 k) n = true ∧ m.canWrite (a + BitVec.ofNat 64 k) n = true := by
  have e : ∀ i, a + BitVec.ofNat 64 k + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (k + i) := by
    intro i; rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨canRead_of (fun i hi => ?_), canWrite_of (fun i hi => ?_)⟩
  · rw [e]; have := sat_bytes_read hs (k + i) (by omega); rw [this.2.1]; exact ⟨rfl, this.2.2⟩
  · rw [e]; exact (sat_bytes_read hs (k + i) (by omega)).2.1

theorem memRegion_append (a : BitVec 64) (n : Nat) (bs : List (BitVec 8)) (hn : n < 2 ^ 64) :
    (memRegion a n ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bs)) ⊢ memRegion a (n + bs.length) := by
  intro h hh
  obtain ⟨h1, h2, hd, rfl, hm, hb⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨b0, hb0⟩ := memRegion_entails_bytes a n hn h1 hm
  obtain ⟨hl, hb0⟩ := pure_sepConj_holds.mp hb0
  have : (a ↦ₛ (b0 ++ bs)).holds (h1.union h2) := by
    rw [pointsToBytes_append, hl]
    exact SepProp.holds_sepConj_iff.mpr ⟨h1, h2, hd, rfl, hb0, hb⟩
  have := bytes_entails_memRegion a _ _ this
  simpa [hl] using this

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem zext12_lit (n : Nat) : BitVec.zeroExtend 64 (BitVec.ofNat 12 n) = BitVec.ofNat 64 (n % 4096) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

theorem zext16_lit (n : Nat) : BitVec.zeroExtend 64 (BitVec.ofNat 16 n) = BitVec.ofNat 64 (n % 65536) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

@[simp] theorem bf_beq_1 : (BitfieldOp.BFM == BitfieldOp.UBFM) = false := by decide
@[simp] theorem bf_beq_2 : (BitfieldOp.BFM == BitfieldOp.SBFM) = false := by decide
@[simp] theorem bf_beq_3 : (BitfieldOp.UBFM == BitfieldOp.SBFM) = false := by decide
@[simp] theorem bf_beq_4 : (BitfieldOp.SBFM == BitfieldOp.UBFM) = false := by decide
@[simp] theorem bf_beq_5 : (BitfieldOp.UBFM == BitfieldOp.UBFM) = true := by decide
@[simp] theorem bf_beq_6 : (BitfieldOp.SBFM == BitfieldOp.SBFM) = true := by decide

end X25519Dalek.LP

namespace X25519Dalek.LP
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

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem add_sub_cancel' (a b : BitVec 64) : a + (b - a) = b := by bv_omega
theorem sub_add_cancel' (a : BitVec 64) (k : Nat) : a - BitVec.ofNat 64 k + BitVec.ofNat 64 k = a := by
  bv_omega

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem memRegion_split (a : BitVec 64) (n k : Nat) (h : n + k < 2 ^ 64) :
    memRegion a (n + k) ⊢ memRegion a n ∗ memRegion (a + BitVec.ofNat 64 n) k := by
  intro hp hh
  obtain ⟨bs, hb⟩ := memRegion_entails_bytes a (n + k) h hp hh
  obtain ⟨hl, hb⟩ := pure_sepConj_holds.mp hb
  rw [pointsToBytes_split a bs n (by omega)] at hb
  obtain ⟨h1, h2, hd, rfl, hb1, hb2⟩ := SepProp.holds_sepConj_iff.mp hb
  refine SepProp.holds_sepConj_iff.mpr ⟨h1, h2, hd, rfl, ?_, ?_⟩
  · have := bytes_entails_memRegion a (bs.take n) h1 hb1; simpa [hl, show n ≤ n + k by omega] using this
  · have := bytes_entails_memRegion _ (bs.drop n) h2 hb2; simpa [hl] using this

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

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem addr_sub_sub (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 ((a + b) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem sat_mr_split {m : Memory} {a : BitVec 64} {F : SepProp} (n k : Nat) (h : n + k < 2 ^ 64)
    (b : BitVec 64) (hb : a + BitVec.ofNat 64 n = b) (hs : m ⊨ memRegion a (n + k) ∗ F) :
    m ⊨ memRegion a n ∗ memRegion b k ∗ F := by
  have := sat_sep_mono hs (memRegion_split a n k h)
  rw [sepConj_assoc, hb] at this; exact this

end X25519Dalek.LP

namespace X25519Dalek.LP

end X25519Dalek.LP

namespace X25519Dalek.LP
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

end X25519Dalek.LP

namespace X25519Dalek.LP
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

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem sat_pre3 {m : Memory} {φ : Prop} {A B C F : SepProp} (hφ : φ) (hs : m ⊨ A ∗ B ∗ C ∗ F) :
    m ⊨ (⌜φ⌝ ∗ A ∗ B ∗ C) ∗ F := by
  rw [sepConj_assoc, sat_pure_sep]; exact ⟨hφ, by simpa only [sepConj_assoc] using hs⟩

end X25519Dalek.LP

namespace X25519Dalek.LP
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

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem sat_mr_merge {m : Memory} {a b : BitVec 64} {F : SepProp} (n k : Nat) (h : n + k < 2 ^ 64)
    (hb : b = a + BitVec.ofNat 64 n) (hs : m ⊨ memRegion a n ∗ memRegion b k ∗ F) :
    m ⊨ memRegion a (n + k) ∗ F := by
  subst hb
  rw [← sepConj_assoc] at hs
  refine sat_sep_mono hs ?_
  intro hp hh
  obtain ⟨h1, h2, hd, rfl, hm1, hm2⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨bs, hb⟩ := memRegion_entails_bytes _ k (by omega) h2 hm2
  obtain ⟨hl, hb⟩ := pure_sepConj_holds.mp hb
  have := memRegion_append a n bs (by omega) _ (SepProp.holds_sepConj_iff.mpr ⟨h1, h2, hd, rfl, hm1, hb⟩)
  rwa [hl] at this

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem sat_mr_bytes {m : Memory} {a b : BitVec 64} {bs : List (BitVec 8)} {F : SepProp} (n : Nat)
    (hn : n < 2 ^ 64) (hb : b = a + BitVec.ofNat 64 n) (hs : m ⊨ memRegion a n ∗ (b ↦ₛ bs) ∗ F) :
    m ⊨ memRegion a (n + bs.length) ∗ F := by
  subst hb
  rw [← sepConj_assoc] at hs
  exact sat_sep_mono hs (memRegion_append a n bs hn)

end X25519Dalek.LP

namespace X25519Dalek.LP

end X25519Dalek.LP

end
end

section
section
/-! # Relocated `ADRP`/`ADD` (and their relaxed `NOP`/`ADR` form): loading a `.rodata` address

Decoding lemmas copied from the sibling batch's `Solutions/X25519DalekEdwards/Reloc.lean`, itself from
the zlib CRC-32 mission's `ZlibCrc32.Small.RelocBase`/`RelocTab`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

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
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  interval_cases i <;> (try simp only [decide_eq_decide]) <;> (try split at h1) <;> omega

theorem hi_bits20 (D : BitVec 64) (h1 : -(2^20:Int) ≤ D.toInt) (h2 : D.toInt < 2^20) :
    ∀ i, 20 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 20 := by
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

theorem page_add_lo (T : BitVec 64) : pageOf T + (T.extractLsb' 0 12).setWidth 64 = T := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, pageOf_toNat]
  simp [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat]
  have := T.isLt; omega


theorem decode_nop : decode nopWord = some .nop := by decide


section words
variable (D : BitVec 64)

end words

end X25519Dalek.LP

end
end

section
section
/-! # One lemma per instruction shape

Each lemma executes one instruction of a given shape from an abstract state `mkS s0 pc r sp ps m v`,
so a block proof applies a lemma per instruction instead of re-running the evaluator `simp` each time
(smaller proof terms). Register operands other than `xzr`/`sp` carry side conditions `≠ 31#5`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64

section
variable {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem y_andi {d a : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) {k : BitVec 64} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalImm .W64 .AND (.gpr d) (.gpr a) k))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r a &&& k)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha]
  exact h

theorem y_mov {d b : BitVec 5} (hd : d ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W64 .ORR (.gpr d) .xzr (.gpr b) .LSL 0))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r b)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, hb, BitVec.zero_or]
  exact h

theorem y_ldp_r {d1 d2 b : BitVec 5} {off A A8 w1 w2 : BitVec 64} (hd1 : d1 ≠ 31#5) (hd2 : d2 ≠ 31#5) (hb : b ≠ 31#5) (hA : r b + off = A) (hA8 : A + 8#64 = A8) (c1 : m.canRead A 8 = true) (c2 : m.canRead A8 8 = true) (e1 : m.read64 A = w1) (e2 : m.read64 A8 = w2) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldp .W64 false (.gpr d1) (.gpr d2) (.Offset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) (upd (upd r d1 w1) d2 w2) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd1, hd2, hb, hA, hA8, c1, c2, e1, e2]
  exact h

theorem y_ldp_sp {d1 d2 : BitVec 5} {off A A8 w1 w2 : BitVec 64} (hd1 : d1 ≠ 31#5) (hd2 : d2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (hA8 : A + 8#64 = A8) (c1 : m.canRead A 8 = true) (c2 : m.canRead A8 8 = true) (e1 : m.read64 A = w1) (e2 : m.read64 A8 = w2) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldp .W64 false (.gpr d1) (.gpr d2) (.Offset .sp off)))
    (h : Reach p (mkS s0 (pc + 4#64) (upd (upd r d1 w1) d2 w2) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd1, hd2, hal, hA, hA8, c1, c2, e1, e2]
  exact h

theorem y_ldr_r {d b : BitVec 5} {off A w : BitVec 64} (hd : d ≠ 31#5) (hb : b ≠ 31#5) (hA : r b + off = A) (c : m.canRead A 8 = true) (e : m.read64 A = w) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldr .W64 .X64 false (.gpr d) (.UnscaledOffset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d w) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, hb, hA, c, e]
  exact h

theorem y_stp_sp {t1 t2 : BitVec 5} {off A A8 : BitVec 64} (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (hA8 : A + 8#64 = A8) (c1 : m.canWrite A 8 = true) (c2 : m.canWrite A8 8 = true) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stp .W64 (.gpr t1) (.gpr t2) (.Offset .sp off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps ((m.write64 A (r t1)).write64 A8 (r t2)) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', ht1, ht2, hal, hA, hA8, c1, c2]
  exact h

theorem y_str_sp {t : BitVec 5} {off A : BitVec 64} (ht : t ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A) (c : m.canWrite A 8 = true) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .X64 (.gpr t) (.Offset .sp off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps (m.write64 A (r t)) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', ht, hal, hA, c]
  exact h

theorem y_str_r {t b : BitVec 5} {off A : BitVec 64} (ht : t ≠ 31#5) (hb : b ≠ 31#5) (hA : r b + off = A) (c : m.canWrite A 8 = true) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .X64 (.gpr t) (.UnscaledOffset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps (m.write64 A (r t)) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', ht, hb, hA, c]
  exact h

theorem y_addi_sp {d : BitVec 5} {k : BitVec 12} (hd : d ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .ADD (.gpr d) .sp k false))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (sp + k.setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, BitVec.truncate_eq_setWidth]
  exact h

theorem y_subi_r {d a : BitVec 5} {k : BitVec 12} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUB (.gpr d) (.gpr a) k false))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r a - k.setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, BitVec.truncate_eq_setWidth]
  exact h

theorem y_movz32 {d : BitVec 5} {k : BitVec 16} (hd : d ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.moveWide .W32 .MOVZ (.gpr d) k 0))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (((k.setWidth 64).setWidth 32).setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, BitVec.truncate_eq_setWidth]
  exact h

end

theorem pc4 (b : BitVec 64) (k l : Nat) (h : k + 4 = l) :
    b + BitVec.ofNat 64 k + 4#64 = b + BitVec.ofNat 64 l := by
  subst h; rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem w8 (a : BitVec 64) (i : Nat) :
    a + BitVec.ofNat 64 (8 * i) + 8#64 = a + BitVec.ofNat 64 (8 * (i + 1)) := by
  rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
  congr 2

/-- Word `i` of a word list at position 1, 2, 3 or 4 of a separating conjunction. -/
theorem wf1 {m : Memory} {a : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (i : Nat) (hi : i < ws.length) :
    m.read64 (a + BitVec.ofNat 64 (8 * i)) = ws.getD i 0 ∧
      m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true := by
  obtain ⟨h1, h2, -⟩ := sat_words_read hs i hi
  refine ⟨?_, h2⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

section
variable {p : Program} {s0 : State} {pc pc' : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem x_andi {d a : BitVec 5} {k x : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalImm .W64 .AND (.gpr d) (.gpr a) k))
    (hpc : pc + 4#64 = pc') (ex : r a = x)
    (h : ∀ t, t = x &&& k → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_andi hd ha hrun hf (h _ rfl)

theorem x_mov {d b : BitVec 5} {y : BitVec 64} (hd : d ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W64 .ORR (.gpr d) .xzr (.gpr b) .LSL 0))
    (hpc : pc + 4#64 = pc') (ey : r b = y)
    (h : Reach p (mkS s0 pc' (upd r d y) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ey; exact y_mov hd hb hrun hf h

/-- `ldp` from a general register base: the two words come with their read facts. -/
theorem x_ldp_r {d1 d2 b : BitVec 5} {off x a w1 w2 : BitVec 64} {i : Nat} {B : BitVec 64} (hd1 : d1 ≠ 31#5)
    (hd2 : d2 ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldp .W64 false (.gpr d1) (.gpr d2) (.Offset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * i))
    (f1 : m.read64 (a + BitVec.ofNat 64 (8 * i)) = w1 ∧ m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true)
    (hB : a + BitVec.ofNat 64 (8 * (i + 1)) = B)
    (f2 : m.read64 B = w2 ∧ m.canRead B 8 = true)
    (h : Reach p (mkS s0 pc' (upd (upd r d1 w1) d2 w2) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_ldp_r hd1 hd2 hb hA ((w8 a i).trans hB) f1.2 f2.2 f1.1 f2.1 hrun hf h

theorem x_ldp_sp {d1 d2 : BitVec 5} {off a w1 w2 : BitVec 64} {i : Nat} {B : BitVec 64} (hd1 : d1 ≠ 31#5)
    (hd2 : d2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldp .W64 false (.gpr d1) (.gpr d2) (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * i))
    (f1 : m.read64 (a + BitVec.ofNat 64 (8 * i)) = w1 ∧ m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true)
    (hB : a + BitVec.ofNat 64 (8 * (i + 1)) = B)
    (f2 : m.read64 B = w2 ∧ m.canRead B 8 = true)
    (h : Reach p (mkS s0 pc' (upd (upd r d1 w1) d2 w2) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; exact y_ldp_sp hd1 hd2 hal hA ((w8 a i).trans hB) f1.2 f2.2 f1.1 f2.1 hrun hf h

/-- Stores into word `i` (and `i + 1`) of the word list at position 1. -/
theorem x_stp_sp {t1 t2 : BitVec 5} {off a v1 v2 : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    {i : Nat} (ht1 : t1 ≠ 31#5) (ht2 : t2 ≠ 31#5) (hal : (sp &&& 15#64) = 0#64)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stp .W64 (.gpr t1) (.gpr t2) (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hi : i + 1 < ws.length) (e1 : r t1 = v1) (e2 : r t2 = v2)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (ws.set i v1).set (i + 1) v2) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc e1 e2
  obtain ⟨-, -, c1⟩ := sat_words_read hs i (by omega)
  obtain ⟨-, -, c2⟩ := sat_words_read hs (i + 1) hi
  refine y_stp_sp ht1 ht2 hal hA (w8 a i) c1 c2 hrun hf ?_
  exact Reach.wr64x2 i hs rfl rfl hi h

theorem x_str_sp {t : BitVec 5} {off a v1 : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    {i : Nat} (ht : t ≠ 31#5) (hal : (sp &&& 15#64) = 0#64)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .X64 (.gpr t) (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hi : i < ws.length) (e1 : r t = v1)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* ws.set i v1) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc e1
  obtain ⟨-, -, c1⟩ := sat_words_read hs i hi
  refine y_str_sp ht hal hA c1 hrun hf ?_
  exact Reach.wr64 i hs rfl hi h

theorem x_str_r {t b : BitVec 5} {off x a v1 : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    {i : Nat} (ht : t ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .X64 (.gpr t) (.UnscaledOffset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hi : i < ws.length) (e1 : r t = v1)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* ws.set i v1) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex e1
  obtain ⟨-, -, c1⟩ := sat_words_read hs i hi
  refine y_str_r ht hb hA c1 hrun hf ?_
  exact Reach.wr64 i hs rfl hi h

end

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
variable {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem y_ldpq_o {t1 t2 b : BitVec 5} {off A A16 lo1 hi1 lo2 hi2 : BitVec 64} (hb : b ≠ 31#5)
    (hA : r b + off = A) (hA16 : A + 16#64 = A16) (c1 : m.canRead A 16 = true)
    (c2 : m.canRead A16 16 = true) (e1 : m.read64 A = lo1) (e2 : m.read64 (A + 8#64) = hi1)
    (e3 : m.read64 A16 = lo2) (e4 : m.read64 (A16 + 8#64) = hi2)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldpSimd .Q128 t1 t2 (.Offset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps m (upd (upd v t1 (hi1 ++ lo1)) t2 (hi2 ++ lo2))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hb, hA, hA16, c1, c2, e1, e2, e3, e4]
  exact h

theorem y_strq_u {t b : BitVec 5} {off A A8 lo hi : BitVec 64} (hb : b ≠ 31#5)
    (hA : r b + off = A) (hA8 : A + 8#64 = A8) (c : m.canWrite A 16 = true) (ev : v t = hi ++ lo)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.strSimd .Q128 t (.UnscaledOffset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps ((m.write64 A lo).write64 A8 hi) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hb, hA, hA8, c, ev]
  exact h

end

section
variable {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem y_subsp {k : BitVec 12} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUB .sp .sp k false))
    (h : Reach p (mkS s0 (pc + 4#64) r (sp - k.setWidth 64) ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', BitVec.truncate_eq_setWidth]
  exact h

theorem y_addsp {k : BitVec 12} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .ADD .sp .sp k false))
    (h : Reach p (mkS s0 (pc + 4#64) r (sp + k.setWidth 64) ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', BitVec.truncate_eq_setWidth]
  exact h

theorem y_ret (hrun : s0.status = .Running) (hf : p.fetchMem m pc = some (.ret (.gpr 30#5)))
    (h : Reach p (mkS s0 (r 30#5) r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel']
  exact h

end

end X25519Dalek.LP

end
end

section
section
/-! # More instruction-shape wrappers: stack-pointer arithmetic, pre/post-indexed pairs, `ret`,
128-bit loads and stores on word lists, and address normalisation `S - a + b = S - c + d` -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64

theorem aSS (S : BitVec 64) (a b c d : Nat)
    (h : BitVec.ofNat 64 b - BitVec.ofNat 64 a = BitVec.ofNat 64 d - BitVec.ofNat 64 c) :
    S - BitVec.ofNat 64 a + BitVec.ofNat 64 b = S - BitVec.ofNat 64 c + BitVec.ofNat 64 d := by
  have e1 : S - BitVec.ofNat 64 a + BitVec.ofNat 64 b = S + (BitVec.ofNat 64 b - BitVec.ofNat 64 a) := by abel
  have e2 : S - BitVec.ofNat 64 c + BitVec.ofNat 64 d = S + (BitVec.ofNat 64 d - BitVec.ofNat 64 c) := by abel
  rw [e1, e2, h]

theorem aSk (S : BitVec 64) (a c : Nat) (k : BitVec 12)
    (h : BitVec.ofNat 64 a - k.setWidth 64 = BitVec.ofNat 64 c) :
    S - BitVec.ofNat 64 a + k.setWidth 64 = S - BitVec.ofNat 64 c := by
  rw [← h]; try abel

theorem aSmk (S : BitVec 64) (a c : Nat) (k : BitVec 12)
    (h : BitVec.ofNat 64 a + k.setWidth 64 = BitVec.ofNat 64 c) :
    S - BitVec.ofNat 64 a - k.setWidth 64 = S - BitVec.ofNat 64 c := by
  rw [← h]; try abel

theorem aSb (S : BitVec 64) (a b c : Nat) (h : BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 c) :
    S - BitVec.ofNat 64 a + BitVec.ofNat 64 b = S - BitVec.ofNat 64 c := by
  rw [← h]; try abel

theorem aS16 (A : BitVec 64) (i : Nat) :
    A + BitVec.ofNat 64 (8 * i) + 16#64 = A + BitVec.ofNat 64 (8 * (i + 2)) := by
  rw [BitVec.add_assoc, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
  congr 2

section
variable {p : Program} {s0 : State} {pc pc' : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem x_addi_sp2 {d : BitVec 5} {k : BitVec 12} {x : BitVec 64} (hd : d ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .ADD (.gpr d) .sp k false))
    (hpc : pc + 4#64 = pc') (hx : sp + k.setWidth 64 = x)
    (h : Reach p (mkS s0 pc' (upd r d x) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc hx; exact y_addi_sp hd hrun hf h

theorem x_subi_r2 {d a : BitVec 5} {k : BitVec 12} {y x : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUB (.gpr d) (.gpr a) k false))
    (hpc : pc + 4#64 = pc') (ey : r a = y) (hx : y - k.setWidth 64 = x)
    (h : Reach p (mkS s0 pc' (upd r d x) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ey hx; exact y_subi_r hd ha hrun hf h

theorem x_subsp {k : BitVec 12} {sp' : BitVec 64} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUB .sp .sp k false))
    (hpc : pc + 4#64 = pc') (hx : sp - k.setWidth 64 = sp')
    (h : Reach p (mkS s0 pc' r sp' ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc hx; exact y_subsp hrun hf h

theorem x_addsp {k : BitVec 12} {sp' : BitVec 64} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .ADD .sp .sp k false))
    (hpc : pc + 4#64 = pc') (hx : sp + k.setWidth 64 = sp')
    (h : Reach p (mkS s0 pc' r sp' ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc hx; exact y_addsp hrun hf h

theorem x_ret {x : BitVec 64} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ret (.gpr 30#5))) (ex : r 30#5 = x)
    (h : Reach p (mkS s0 x r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst ex; exact y_ret hrun hf h

theorem x_ldr_u {d b : BitVec 5} {off x a w : BitVec 64} {i : Nat} (hd : d ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldr .W64 .X64 false (.gpr d) (.UnscaledOffset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * i))
    (f1 : m.read64 (a + BitVec.ofNat 64 (8 * i)) = w ∧ m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true)
    (h : Reach p (mkS s0 pc' (upd r d w) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_ldr_r hd hb hA f1.2 f1.1 hrun hf h

theorem x_ldpq_o {t1 t2 b : BitVec 5} {off x a lo1 hi1 lo2 hi2 : BitVec 64} {i : Nat} (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldpSimd .Q128 t1 t2 (.Offset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * i))
    (f1 : m.read64 (a + BitVec.ofNat 64 (8 * i)) = lo1 ∧ m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true)
    (f2 : m.read64 (a + BitVec.ofNat 64 (8 * (i + 1))) = hi1 ∧
      m.canRead (a + BitVec.ofNat 64 (8 * (i + 1))) 8 = true)
    (f3 : m.read64 (a + BitVec.ofNat 64 (8 * (i + 2))) = lo2 ∧
      m.canRead (a + BitVec.ofNat 64 (8 * (i + 2))) 8 = true)
    (f4 : m.read64 (a + BitVec.ofNat 64 (8 * (i + 3))) = hi2 ∧
      m.canRead (a + BitVec.ofNat 64 (8 * (i + 3))) 8 = true)
    (h : Reach p (mkS s0 pc' r sp ps m (upd (upd v t1 (hi1 ++ lo1)) t2 (hi2 ++ lo2))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex
  have g2 : m.canRead (a + BitVec.ofNat 64 (8 * i) + 8#64) 8 = true := by rw [w8]; exact f2.2
  have g4 : m.canRead (a + BitVec.ofNat 64 (8 * (i + 2)) + 8#64) 8 = true := by rw [w8]; exact f4.2
  have r2 : m.read64 (a + BitVec.ofNat 64 (8 * i) + 8#64) = hi1 := by rw [w8]; exact f2.1
  have r4 : m.read64 (a + BitVec.ofNat 64 (8 * (i + 2)) + 8#64) = hi2 := by rw [w8]; exact f4.1
  exact y_ldpq_o hb hA (aS16 a i) (canRead16 f1.2 g2) (canRead16 f3.2 g4) f1.1 r2 f3.1 r4 hrun hf h

theorem x_strq_u {t b : BitVec 5} {off x a lo hi : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    {i : Nat} (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.strSimd .Q128 t (.UnscaledOffset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hl : i + 1 < ws.length) (ev : v t = hi ++ lo)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (ws.set i lo).set (i + 1) hi) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex
  obtain ⟨-, -, c1⟩ := sat_words_read hs i (by omega)
  obtain ⟨-, -, c2⟩ := sat_words_read hs (i + 1) hl
  rw [← w8] at c2
  refine y_strq_u hb hA (w8 a i) (canWrite16 c1 c2) ev hrun hf ?_
  exact Reach.wr64x2 i hs rfl rfl hl h

end


theorem reach_reg {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
    {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop} {i : BitVec 5} {x : BitVec 64}
    (h : r i = x) (hr : Reach p (mkS s0 pc (upd r i x) sp ps m v) Q) : Reach p (mkS s0 pc r sp ps m v) Q := by
  have e : upd r i x = r := by
    funext k; simp only [upd]; split_ifs with hk
    · subst hk; exact h.symm
    · rfl
  rwa [e] at hr


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

end X25519Dalek.LP

end
end

section
section
/-! # Instruction shapes for block 15 (`MontgomeryPoint * Scalar`) -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64

theorem sw_32_64 (x : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 x) = x := by
  ext i hi; simp [BitVec.getElem_setWidth]
theorem sw32_xor (a b : BitVec 64) : BitVec.setWidth 32 (a ^^^ b) = a.setWidth 32 ^^^ b.setWidth 32 := by
  ext i hi; simp [BitVec.getElem_setWidth]
theorem sw32_and (a b : BitVec 64) : BitVec.setWidth 32 (a &&& b) = a.setWidth 32 &&& b.setWidth 32 := by
  ext i hi; simp [BitVec.getElem_setWidth]
theorem sw32_or (a b : BitVec 64) : BitVec.setWidth 32 (a ||| b) = a.setWidth 32 ||| b.setWidth 32 := by
  ext i hi; simp [BitVec.getElem_setWidth]

section
variable {p : Program} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem y_movi0 (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.simdImmShift true true 0#4 0#3 28#5 0#5 0#5))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps m (upd v 0#5 0#128)) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_ldr_o {d b : BitVec 5} {off A w : BitVec 64} (hd : d ≠ 31#5) (hb : b ≠ 31#5) (hA : r b + off = A)
    (c : m.canRead A 8 = true) (e : m.read64 A = w) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldr .W64 .X64 false (.gpr d) (.Offset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d w) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, hb, hA, c, e, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_movzr64 {d : BitVec 5} (hd : d ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W64 .ORR (.gpr d) .xzr .xzr .LSL 0))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d 0#64) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_movzr32 {d : BitVec 5} (hd : d ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W32 .ORR (.gpr d) .xzr .xzr .LSL 0))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d 0#64) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_movw {d b : BitVec 5} (hd : d ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W32 .ORR (.gpr d) .xzr (.gpr b) .LSL 0))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (((r b).setWidth 32).setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, hb, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_ubfm {d a : BitVec 5} {i j : Nat} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.bitfield .W64 .UBFM (.gpr d) (.gpr a) i j))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (evalBitfield .W64 .UBFM 0#64 (r a) i j)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_eor {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W64 .EOR (.gpr d) (.gpr a) (.gpr b) .LSL 0))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r a ^^^ r b)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, hb, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_and {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W64 .AND (.gpr d) (.gpr a) (.gpr b) .LSL 0))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r a &&& r b)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, hb, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_orr {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W64 .ORR (.gpr d) (.gpr a) (.gpr b) .LSL 0))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r a ||| r b)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, hb, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_eorw {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W32 .EOR (.gpr d) (.gpr a) (.gpr b) .LSL 0))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (((r a).setWidth 32 ^^^ (r b).setWidth 32).setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, hb, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_andiw {d a : BitVec 5} {k : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalImm .W32 .AND (.gpr d) (.gpr a) k))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (((r a).setWidth 32 &&& k.setWidth 32).setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_lsrvw {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.dataProc2 .W32 .LSRV (.gpr d) (.gpr a) (.gpr b)))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (BitVec.setWidth 64 (BitVec.setWidth 32 (r a) >>> ((BitVec.setWidth 32 (r b)).toNat % 32)))) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, hb, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_subuxtb {d a b : BitVec 5} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubExt .W64 .SUB (.gpr d) (.gpr a) (.gpr b) .UXTB 0))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r a - ((r b).setWidth 8).setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, hb, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_neg {d b : BitVec 5} (hd : d ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubShift .W64 .SUB (.gpr d) .xzr (.gpr b) .LSL 0))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (0#64 - r b)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, hb, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_subi {d a : BitVec 5} {k : BitVec 12} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUB (.gpr d) (.gpr a) k false))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (r a - k.setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, ha, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_cmp {a b : BitVec 5} (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubShift .W64 .SUBS .xzr (.gpr a) (.gpr b) .LSL 0))
    (h : Reach p (mkS s0 (pc + 4#64) r sp (AddWithCarry64 (r a) (~~~(r b)) true).2 m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', ha, hb, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_cmpi {a : BitVec 5} {k : BitVec 12} (ha : a ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUBS .xzr (.gpr a) k false))
    (h : Reach p (mkS s0 (pc + 4#64) r sp (AddWithCarry64 (r a) (~~~(k.setWidth 64)) true).2 m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', ha, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_cmpiw {a : BitVec 5} {k : BitVec 12} (ha : a ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W32 .SUBS .xzr (.gpr a) k false))
    (h : Reach p (mkS s0 (pc + 4#64) r sp (AddWithCarry32 (BitVec.setWidth 32 (r a)) (~~~BitVec.setWidth 32 (BitVec.setWidth 64 k)) true).2 m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', ha, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_bcond {c : CondCode} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.bCond c off))
    (h : Reach p (mkS s0 (if ConditionHolds c ps then pc + off else pc + 4#64) r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc]
  split <;> simp_all

theorem y_b {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.b off))
    (h : Reach p (mkS s0 (pc + off) r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_cbnz {t : BitVec 5} {off : BitVec 64} (ht : t ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.cbz .W64 true (.gpr t) off))
    (h : Reach p (mkS s0 (if r t = 0#64 then pc + 4#64 else pc + off) r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, State.readReg, mkS_readGpr, ht, if_false]
  by_cases hc : r t = 0#64 <;> simp_all

theorem y_cbz {t : BitVec 5} {off : BitVec 64} (ht : t ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.cbz .W64 false (.gpr t) off))
    (h : Reach p (mkS s0 (if r t = 0#64 then pc + off else pc + 4#64) r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, State.readReg, mkS_readGpr, ht, if_false]
  by_cases hc : r t = 0#64 <;> simp_all

theorem y_ldrb_reg {d b i : BitVec 5} {A : BitVec 64} {w : BitVec 8} (hd : d ≠ 31#5) (hb : b ≠ 31#5) (hi : i ≠ 31#5)
    (hA : r b + r i = A) (c : m.canRead A 1 = true) (e : m.read8 A = w) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldr .W32 .B8 false (.gpr d) (.RegOffset (.gpr b) (.gpr i) .UXTX 0)))
    (h : Reach p (mkS s0 (pc + 4#64) (upd r d (((w.setWidth 64).setWidth 32).setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hd, hb, hi, hA, c, e, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_strb_u {t b : BitVec 5} {off A : BitVec 64} (ht : t ≠ 31#5) (hb : b ≠ 31#5) (hA : r b + off = A)
    (c : m.canWrite A 1 = true) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .B8 (.gpr t) (.UnscaledOffset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps (m.write8 A ((r t).setWidth 8)) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', ht, hb, hA, c, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_strbzr_u {b : BitVec 5} {off A : BitVec 64} (hb : b ≠ 31#5) (hA : r b + off = A)
    (c : m.canWrite A 1 = true) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .B8 .xzr (.UnscaledOffset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps (m.write8 A 0#8) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hb, hA, c, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_strzr_sp {off A : BitVec 64} (hal : (sp &&& 15#64) = 0#64) (hA : sp + off = A)
    (c : m.canWrite A 8 = true) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .X64 .xzr (.Offset .sp off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps (m.write64 A 0#64) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hal, hA, c, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_stpzr_r {t1 b : BitVec 5} {off A A8 : BitVec 64} (ht1 : t1 ≠ 31#5) (hb : b ≠ 31#5)
    (hA : r b + off = A) (hA8 : A + 8#64 = A8) (c1 : m.canWrite A 8 = true) (c2 : m.canWrite A8 8 = true)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stp .W64 (.gpr t1) .xzr (.Offset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps ((m.write64 A (r t1)).write64 A8 0#64) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', ht1, hb, hA, hA8, c1, c2, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_strq_spu {t : BitVec 5} {off A A8 lo hi : BitVec 64} (hal : (sp &&& 15#64) = 0#64)
    (hA : sp + off = A) (hA8 : A + 8#64 = A8) (c : m.canWrite A 16 = true) (ev : v t = hi ++ lo)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.strSimd .Q128 t (.UnscaledOffset .sp off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps ((m.write64 A lo).write64 A8 hi) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hal, hA, hA8, c, ev, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_strq_spo {t : BitVec 5} {off A A8 lo hi : BitVec 64} (hal : (sp &&& 15#64) = 0#64)
    (hA : sp + off = A) (hA8 : A + 8#64 = A8) (c : m.canWrite A 16 = true) (ev : v t = hi ++ lo)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.strSimd .Q128 t (.Offset .sp off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps ((m.write64 A lo).write64 A8 hi) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hal, hA, hA8, c, ev, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_ldrq_spu {t : BitVec 5} {off A lo hi : BitVec 64} (hal : (sp &&& 15#64) = 0#64)
    (hA : sp + off = A) (c : m.canRead A 16 = true) (e1 : m.read64 A = lo) (e2 : m.read64 (A + 8#64) = hi)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldrSimd .Q128 t (.UnscaledOffset .sp off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps m (upd v t (hi ++ lo))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hal, hA, c, e1, e2, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

theorem y_stpq_sp {t1 t2 : BitVec 5} {off A A8 A16 A24 lo1 hi1 lo2 hi2 : BitVec 64} (hal : (sp &&& 15#64) = 0#64)
    (hA : sp + off = A) (hA8 : A + 8#64 = A8) (hA16 : A + 16#64 = A16) (hA24 : A16 + 8#64 = A24)
    (c1 : m.canWrite A 16 = true) (c2 : m.canWrite A16 16 = true) (ev1 : v t1 = hi1 ++ lo1)
    (ev2 : v t2 = hi2 ++ lo2) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stpSimd .Q128 t1 t2 (.Offset .sp off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps ((((m.write64 A lo1).write64 A8 hi1).write64 A16 lo2).write64 A24 hi2) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hal, hA, hA8, hA16, hA24, c1, c2, ev1, ev2, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h


theorem y_strq_o {t b : BitVec 5} {off A A8 lo hi : BitVec 64} (hb : b ≠ 31#5)
    (hA : r b + off = A) (hA8 : A + 8#64 = A8) (c : m.canWrite A 16 = true) (ev : v t = hi ++ lo)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.strSimd .Q128 t (.Offset (.gpr b) off)))
    (h : Reach p (mkS s0 (pc + 4#64) r sp ps ((m.write64 A lo).write64 A8 hi) v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', hb, hA, hA8, c, ev, BitVec.truncate_eq_setWidth, sw_32_64, sw32_xor, sw32_and, sw32_or, BitVec.zero_or]
  exact h

end

section
variable {p : Program} {s0 : State} {pc pc' : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
  {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}

theorem x_movi0 (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.simdImmShift true true 0#4 0#3 28#5 0#5 0#5)) (hpc : pc + 4#64 = pc')
    (h : Reach p (mkS s0 pc' r sp ps m (upd v 0#5 0#128)) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; exact y_movi0 hrun hf h

theorem x_ldr_any {d b : BitVec 5} {off x A w : BitVec 64} (hd : d ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldr .W64 .X64 false (.gpr d) (.UnscaledOffset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = A) (f : m.read64 A = w ∧ m.canRead A 8 = true)
    (h : Reach p (mkS s0 pc' (upd r d w) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_ldr_r hd hb hA f.2 f.1 hrun hf h

theorem x_ldr_anyo {d b : BitVec 5} {off x A w : BitVec 64} (hd : d ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldr .W64 .X64 false (.gpr d) (.Offset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = A) (f : m.read64 A = w ∧ m.canRead A 8 = true)
    (h : Reach p (mkS s0 pc' (upd r d w) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_ldr_o hd hb hA f.2 f.1 hrun hf h

theorem x_movzr64 {d : BitVec 5} (hd : d ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W64 .ORR (.gpr d) .xzr .xzr .LSL 0)) (hpc : pc + 4#64 = pc')
    (h : Reach p (mkS s0 pc' (upd r d 0#64) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; exact y_movzr64 hd hrun hf h

theorem x_movzr32 {d : BitVec 5} (hd : d ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W32 .ORR (.gpr d) .xzr .xzr .LSL 0)) (hpc : pc + 4#64 = pc')
    (h : Reach p (mkS s0 pc' (upd r d 0#64) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; exact y_movzr32 hd hrun hf h

theorem x_movw {d b : BitVec 5} {y : BitVec 64} (hd : d ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W32 .ORR (.gpr d) .xzr (.gpr b) .LSL 0)) (hpc : pc + 4#64 = pc')
    (ey : r b = y) (h : ∀ t, t = (y.setWidth 32).setWidth 64 → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ey; exact y_movw hd hb hrun hf (h _ rfl)

theorem x_ubfm {d a : BitVec 5} {i j : Nat} {x : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.bitfield .W64 .UBFM (.gpr d) (.gpr a) i j)) (hpc : pc + 4#64 = pc')
    (ex : r a = x) (h : ∀ t, t = evalBitfield .W64 .UBFM 0#64 x i j → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_ubfm hd ha hrun hf (h _ rfl)

theorem x_eor {d a b : BitVec 5} {x y : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W64 .EOR (.gpr d) (.gpr a) (.gpr b) .LSL 0)) (hpc : pc + 4#64 = pc')
    (ex : r a = x) (ey : r b = y) (h : ∀ t, t = x ^^^ y → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex ey; exact y_eor hd ha hb hrun hf (h _ rfl)

theorem x_and {d a b : BitVec 5} {x y : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W64 .AND (.gpr d) (.gpr a) (.gpr b) .LSL 0)) (hpc : pc + 4#64 = pc')
    (ex : r a = x) (ey : r b = y) (h : ∀ t, t = x &&& y → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex ey; exact y_and hd ha hb hrun hf (h _ rfl)

theorem x_orr {d a b : BitVec 5} {x y : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W64 .ORR (.gpr d) (.gpr a) (.gpr b) .LSL 0)) (hpc : pc + 4#64 = pc')
    (ex : r a = x) (ey : r b = y) (h : ∀ t, t = x ||| y → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex ey; exact y_orr hd ha hb hrun hf (h _ rfl)

theorem x_eorw {d a b : BitVec 5} {x y : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalShift .W32 .EOR (.gpr d) (.gpr a) (.gpr b) .LSL 0)) (hpc : pc + 4#64 = pc')
    (ex : r a = x) (ey : r b = y)
    (h : ∀ t, t = (x.setWidth 32 ^^^ y.setWidth 32).setWidth 64 → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex ey; exact y_eorw hd ha hb hrun hf (h _ rfl)

theorem x_andiw {d a : BitVec 5} {k x : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.logicalImm .W32 .AND (.gpr d) (.gpr a) k)) (hpc : pc + 4#64 = pc')
    (ex : r a = x)
    (h : ∀ t, t = (x.setWidth 32 &&& k.setWidth 32).setWidth 64 → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_andiw hd ha hrun hf (h _ rfl)

theorem x_lsrvw {d a b : BitVec 5} {x y : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.dataProc2 .W32 .LSRV (.gpr d) (.gpr a) (.gpr b))) (hpc : pc + 4#64 = pc')
    (ex : r a = x) (ey : r b = y)
    (h : ∀ t, t = BitVec.setWidth 64 (BitVec.setWidth 32 x >>> ((BitVec.setWidth 32 y).toNat % 32)) →
      Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex ey; exact y_lsrvw hd ha hb hrun hf (h _ rfl)

theorem x_subuxtb {d a b : BitVec 5} {x y : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubExt .W64 .SUB (.gpr d) (.gpr a) (.gpr b) .UXTB 0)) (hpc : pc + 4#64 = pc')
    (ex : r a = x) (ey : r b = y)
    (h : ∀ t, t = x - (y.setWidth 8).setWidth 64 → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex ey; exact y_subuxtb hd ha hb hrun hf (h _ rfl)

theorem x_neg {d b : BitVec 5} {y : BitVec 64} (hd : d ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubShift .W64 .SUB (.gpr d) .xzr (.gpr b) .LSL 0)) (hpc : pc + 4#64 = pc')
    (ey : r b = y) (h : ∀ t, t = 0#64 - y → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ey; exact y_neg hd hb hrun hf (h _ rfl)

theorem x_subi {d a : BitVec 5} {k : BitVec 12} {x : BitVec 64} (hd : d ≠ 31#5) (ha : a ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUB (.gpr d) (.gpr a) k false)) (hpc : pc + 4#64 = pc')
    (ex : r a = x) (h : ∀ t, t = x - k.setWidth 64 → Reach p (mkS s0 pc' (upd r d t) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_subi hd ha hrun hf (h _ rfl)

theorem x_cmp {a b : BitVec 5} {x y : BitVec 64} (ha : a ≠ 31#5) (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubShift .W64 .SUBS .xzr (.gpr a) (.gpr b) .LSL 0)) (hpc : pc + 4#64 = pc')
    (ex : r a = x) (ey : r b = y)
    (h : Reach p (mkS s0 pc' r sp (AddWithCarry64 x (~~~y) true).2 m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex ey; exact y_cmp ha hb hrun hf h

theorem x_cmpi {a : BitVec 5} {k : BitVec 12} {x : BitVec 64} (ha : a ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W64 .SUBS .xzr (.gpr a) k false)) (hpc : pc + 4#64 = pc')
    (ex : r a = x) (h : Reach p (mkS s0 pc' r sp (AddWithCarry64 x (~~~(k.setWidth 64)) true).2 m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_cmpi ha hrun hf h

theorem x_cmpiw {a : BitVec 5} {k : BitVec 12} {x : BitVec 64} (ha : a ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.addSubImm .W32 .SUBS .xzr (.gpr a) k false)) (hpc : pc + 4#64 = pc')
    (ex : r a = x)
    (h : Reach p (mkS s0 pc' r sp (AddWithCarry32 (BitVec.setWidth 32 x) (~~~BitVec.setWidth 32 (BitVec.setWidth 64 k)) true).2 m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_cmpiw ha hrun hf h

theorem x_bcond_t {c : CondCode} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.bCond c off)) (hc : ConditionHolds c ps = true) (hpc : pc + off = pc')
    (h : Reach p (mkS s0 pc' r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; exact y_bcond hrun hf (by rw [hc]; exact h)

theorem x_bcond_n {c : CondCode} {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.bCond c off)) (hc : ConditionHolds c ps = false) (hpc : pc + 4#64 = pc')
    (h : Reach p (mkS s0 pc' r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; exact y_bcond hrun hf (by rw [hc]; exact h)

theorem x_b {off : BitVec 64} (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.b off)) (hpc : pc + off = pc')
    (h : Reach p (mkS s0 pc' r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc; exact y_b hrun hf h

theorem x_cbnz_t {t : BitVec 5} {off x : BitVec 64} (ht : t ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.cbz .W64 true (.gpr t) off)) (ex : r t = x) (hx : x ≠ 0#64)
    (hpc : pc + off = pc') (h : Reach p (mkS s0 pc' r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_cbnz ht hrun hf (by rw [if_neg hx]; exact h)

theorem x_cbz_t {t : BitVec 5} {off x : BitVec 64} (ht : t ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.cbz .W64 false (.gpr t) off)) (ex : r t = x) (hx : x = 0#64)
    (hpc : pc + off = pc') (h : Reach p (mkS s0 pc' r sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex; exact y_cbz ht hrun hf (by rw [if_pos hx]; exact h)

theorem x_ldrb_reg {d b i : BitVec 5} {x y A : BitVec 64} {w : BitVec 8} (hd : d ≠ 31#5) (hb : b ≠ 31#5)
    (hi : i ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldr .W32 .B8 false (.gpr d) (.RegOffset (.gpr b) (.gpr i) .UXTX 0)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (ey : r i = y) (hA : x + y = A)
    (f : m.read8 A = w ∧ m.canRead A 1 = true)
    (h : Reach p (mkS s0 pc' (upd r d (((w.setWidth 64).setWidth 32).setWidth 64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex ey; exact y_ldrb_reg hd hb hi hA f.2 f.1 hrun hf h

theorem x_strb_u {t b : BitVec 5} {off x a vb : BitVec 64} {b0 : BitVec 8} {F : SepProp} (ht : t ≠ 31#5)
    (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .B8 (.gpr t) (.UnscaledOffset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a) (hs : m ⊨ (a ↦ₛ [b0]) ∗ F) (ev : r t = vb)
    (h : ∀ m', (m' ⊨ (a ↦ₛ [vb.setWidth 8]) ∗ F) → m.KeepsFrozen m' → Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex ev
  have c : m.canWrite a 1 = true := by simpa using (sat_bytes_access hs 0 1 (by simp)).2
  refine y_strb_u ht hb hA c hrun hf ?_
  refine h _ ?_ (Memory.keepsFrozen_write8 c _)
  have := sat_bytes_write hs 0 (by simp) ((r t).setWidth 8)
  simpa using this

theorem x_strbzr_u {b : BitVec 5} {off x a : BitVec 64} {b0 : BitVec 8} {F : SepProp}
    (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .B8 .xzr (.UnscaledOffset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a) (hs : m ⊨ (a ↦ₛ [b0]) ∗ F)
    (h : ∀ m', (m' ⊨ (a ↦ₛ [0#8]) ∗ F) → m.KeepsFrozen m' → Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex
  have c : m.canWrite a 1 = true := by simpa using (sat_bytes_access hs 0 1 (by simp)).2
  refine y_strbzr_u hb hA c hrun hf ?_
  refine h _ ?_ (Memory.keepsFrozen_write8 c _)
  have := sat_bytes_write hs 0 (by simp) 0#8
  simpa using this

theorem x_strzr_sp {off a : BitVec 64} {ws : List (BitVec 64)} {F : SepProp} {i : Nat}
    (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.str .X64 .xzr (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hi : i < ws.length)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* ws.set i 0#64) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc
  obtain ⟨-, -, c1⟩ := sat_words_read hs i hi
  refine y_strzr_sp hal hA c1 hrun hf ?_
  exact Reach.wr64 i hs rfl hi h

theorem x_stpzr_r {t1 b : BitVec 5} {off x a v1 : BitVec 64} {ws : List (BitVec 64)}
    {F : SepProp} {i : Nat} (ht1 : t1 ≠ 31#5) (hb : b ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stp .W64 (.gpr t1) .xzr (.Offset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hi : i + 1 < ws.length) (e1 : r t1 = v1)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (ws.set i v1).set (i + 1) 0#64) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex e1
  obtain ⟨-, -, c1⟩ := sat_words_read hs i (by omega)
  obtain ⟨-, -, c2⟩ := sat_words_read hs (i + 1) hi
  refine y_stpzr_r ht1 hb hA (w8 a i) c1 c2 hrun hf ?_
  exact Reach.wr64x2 i hs rfl rfl hi h

theorem x_strq_spu {t : BitVec 5} {off a lo hi : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    {i : Nat} (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.strSimd .Q128 t (.UnscaledOffset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hl : i + 1 < ws.length) (ev : v t = hi ++ lo)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (ws.set i lo).set (i + 1) hi) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc
  obtain ⟨-, -, c1⟩ := sat_words_read hs i (by omega)
  obtain ⟨-, -, c2⟩ := sat_words_read hs (i + 1) hl
  rw [← w8] at c2
  refine y_strq_spu hal hA (w8 a i) (canWrite16 c1 c2) ev hrun hf ?_
  exact Reach.wr64x2 i hs rfl rfl hl h

theorem x_strq_spo {t : BitVec 5} {off a lo hi : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    {i : Nat} (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.strSimd .Q128 t (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hl : i + 1 < ws.length) (ev : v t = hi ++ lo)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (ws.set i lo).set (i + 1) hi) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc
  obtain ⟨-, -, c1⟩ := sat_words_read hs i (by omega)
  obtain ⟨-, -, c2⟩ := sat_words_read hs (i + 1) hl
  rw [← w8] at c2
  refine y_strq_spo hal hA (w8 a i) (canWrite16 c1 c2) ev hrun hf ?_
  exact Reach.wr64x2 i hs rfl rfl hl h

theorem x_ldrq_spu {t : BitVec 5} {off a lo hi : BitVec 64} {i : Nat} (hal : (sp &&& 15#64) = 0#64)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.ldrSimd .Q128 t (.UnscaledOffset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * i))
    (f1 : m.read64 (a + BitVec.ofNat 64 (8 * i)) = lo ∧ m.canRead (a + BitVec.ofNat 64 (8 * i)) 8 = true)
    (f2 : m.read64 (a + BitVec.ofNat 64 (8 * (i + 1))) = hi ∧
      m.canRead (a + BitVec.ofNat 64 (8 * (i + 1))) 8 = true)
    (h : Reach p (mkS s0 pc' r sp ps m (upd v t (hi ++ lo))) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc
  rw [← w8] at f2
  exact y_ldrq_spu hal hA (canRead16 f1.2 f2.2) f1.1 f2.1 hrun hf h

theorem x_stpq_sp {t1 t2 : BitVec 5} {off a lo1 hi1 lo2 hi2 : BitVec 64} {ws : List (BitVec 64)}
    {F : SepProp} {i : Nat} (hal : (sp &&& 15#64) = 0#64) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.stpSimd .Q128 t1 t2 (.Offset .sp off)))
    (hpc : pc + 4#64 = pc') (hA : sp + off = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hi : i + 3 < ws.length) (ev1 : v t1 = hi1 ++ lo1)
    (ev2 : v t2 = hi2 ++ lo2)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (((ws.set i lo1).set (i + 1) hi1).set (i + 2) lo2).set (i + 3) hi2) ∗ F) →
      m.KeepsFrozen m' → Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc
  obtain ⟨-, -, c1⟩ := sat_words_read hs i (by omega)
  obtain ⟨-, -, c2⟩ := sat_words_read hs (i + 1) (by omega)
  obtain ⟨-, -, c3⟩ := sat_words_read hs (i + 2) (by omega)
  obtain ⟨-, -, c4⟩ := sat_words_read hs (i + 3) hi
  have g2 : m.canWrite (a + BitVec.ofNat 64 (8 * i) + 8#64) 8 = true := by rw [w8]; exact c2
  have g4 : m.canWrite (a + BitVec.ofNat 64 (8 * (i + 2)) + 8#64) 8 = true := by rw [w8]; exact c4
  refine y_stpq_sp hal hA (w8 a i) (aS16 a i) (w8 a (i + 2)) (canWrite16 c1 g2) (canWrite16 c3 g4) ev1 ev2
    hrun hf ?_
  exact Reach.wr64x4 i hs rfl rfl rfl rfl hi h

theorem x_strq_o {t b : BitVec 5} {off x a lo hi : BitVec 64} {ws : List (BitVec 64)} {F : SepProp}
    {i : Nat} (hb : b ≠ 31#5) (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.strSimd .Q128 t (.Offset (.gpr b) off)))
    (hpc : pc + 4#64 = pc') (ex : r b = x) (hA : x + off = a + BitVec.ofNat 64 (8 * i))
    (hs : m ⊨ (a ↦₆₄* ws) ∗ F) (hl : i + 1 < ws.length) (ev : v t = hi ++ lo)
    (h : ∀ m', (m' ⊨ (a ↦₆₄* (ws.set i lo).set (i + 1) hi) ∗ F) → m.KeepsFrozen m' →
      Reach p (mkS s0 pc' r sp ps m' v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc ex
  obtain ⟨-, -, c1⟩ := sat_words_read hs i (by omega)
  obtain ⟨-, -, c2⟩ := sat_words_read hs (i + 1) hl
  rw [← w8] at c2
  refine y_strq_o hb hA (w8 a i) (canWrite16 c1 c2) ev hrun hf ?_
  exact Reach.wr64x2 i hs rfl rfl hl h

theorem x_movz32c {d : BitVec 5} {k : BitVec 16} {c : BitVec 64} (hd : d ≠ 31#5)
    (hrun : s0.status = .Running)
    (hf : p.fetchMem m pc = some (.moveWide .W32 .MOVZ (.gpr d) k 0))
    (hpc : pc + 4#64 = pc') (hc : ((k.setWidth 64).setWidth 32).setWidth 64 = c)
    (h : Reach p (mkS s0 pc' (upd r d c) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  subst hpc hc; exact y_movz32 hd hrun hf h

theorem pcb (b : BitVec 64) (k off l : Nat) (h : (k + off) % 2 ^ 64 = l) :
    b + BitVec.ofNat 64 k + BitVec.ofNat 64 off = b + BitVec.ofNat 64 l := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← h]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

theorem cond_cs64 (x y : BitVec 64) :
    ConditionHolds .CS (AddWithCarry64 x (~~~y) true).2 = decide (y.toNat ≤ x.toNat) := by
  simp only [ConditionHolds, AddWithCarry64, BitVec.msb_eq_decide, ite_true]
  congr 1
  apply propext
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_not, BitVec.toNat_ofNat]
  have hx := x.isLt; have hy := y.isLt
  constructor <;> intro h <;> omega

theorem cond_eq32 (x y : BitVec 32) :
    ConditionHolds .EQ (AddWithCarry32 x (~~~y) true).2 = decide (x = y) := by
  simp only [ConditionHolds, AddWithCarry32, ite_true]
  by_cases h : x = y
  · subst h; simp only [decide_true]; apply beq_iff_eq.mpr; bv_omega
  · simp only [h, decide_false]; apply beq_eq_false_iff_ne.mpr; intro e; apply h; bv_omega

end

end X25519Dalek.LP

end
end

section
section
/-! # Block 15: per-offset instruction fetch (generated by tools_ladder/gen_code.py) -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

abbrev callee15_0 : String := "<core::iter::adapters::rev::Rev<core::iter::adapters::map::Map<core::ops::range::Range<usize>, <curve25519_dalek::scalar::Scalar>::bits_le::{closure#0}>> as core::iter::traits::iterator::Iterator>::nth"

abbrev callee15_1 : String := "<curve25519_dalek::montgomery::ProjectivePoint>::as_affine"

abbrev callee15_3 : String := "curve25519_dalek::montgomery::differential_add_and_double"

abbrev callee15_4 : String := "subtle::black_box::<u8>"

theorem blk15 : blk 15 = x25519CliBlk15 := rfl

theorem len15 : x25519CliBlk15.code.length = 844 := by decide +kernel

section
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m0) (j : Nat) {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem c15_0 : (bprog mpl j).fetchMem m (mpl.base 15) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.sp) (Reg.sp) 0x170#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 0) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.sp) (Reg.sp) 0x170#12 false)) (by decide) rfl (by decide +kernel) hk
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

theorem c15_4 : (bprog mpl j).fetchMem m (mpl.base 15 + 4#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.Offset (Reg.sp) 0x0000000000000110#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 4) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.Offset (Reg.sp) 0x0000000000000110#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_8 : (bprog mpl j).fetchMem m (mpl.base 15 + 8#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x1c#5) (Reg.gpr 0x1b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000120#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 8) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x1c#5) (Reg.gpr 0x1b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000120#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_12 : (bprog mpl j).fetchMem m (mpl.base 15 + 12#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000130#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 12) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000130#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_16 : (bprog mpl j).fetchMem m (mpl.base 15 + 16#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x18#5) (Reg.gpr 0x17#5) (AddrMode.Offset (Reg.sp) 0x0000000000000140#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 16) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x18#5) (Reg.gpr 0x17#5) (AddrMode.Offset (Reg.sp) 0x0000000000000140#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_20 : (bprog mpl j).fetchMem m (mpl.base 15 + 20#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x16#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x0000000000000150#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 20) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x16#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x0000000000000150#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_24 : (bprog mpl j).fetchMem m (mpl.base 15 + 24#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000160#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 24) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000160#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_28 : (bprog mpl j).fetchMem m (mpl.base 15 + 28#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x1d#5) (Reg.sp) 0x110#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 28) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x1d#5) (Reg.sp) 0x110#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_32 : (bprog mpl j).fetchMem m (mpl.base 15 + 32#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x09#5) (Reg.xzr) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 32) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x09#5) (Reg.xzr) (Reg.gpr 0x00#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_36 : (bprog mpl j).fetchMem m (mpl.base 15 + 36#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x13#5) (Reg.xzr) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 36) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x13#5) (Reg.xzr) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_40 : (bprog mpl j).fetchMem m (mpl.base 15 + 40#64) =
    some (Instr.simdImmShift true true 0x0#4 0x0#3 0x1c#5 0x00#5 0x00#5) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 40) (inst := (Instr.simdImmShift true true 0x0#4 0x0#3 0x1c#5 0x00#5 0x00#5)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_44 : (bprog mpl j).fetchMem m (mpl.base 15 + 44#64) =
    some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x0a#5) (AddrMode.UnscaledOffset (Reg.gpr 0x00#5) 0x0000000000000006#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 44) (inst := (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x0a#5) (AddrMode.UnscaledOffset (Reg.gpr 0x00#5) 0x0000000000000006#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_48 : (bprog mpl j).fetchMem m (mpl.base 15 + 48#64) =
    some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x00#5) 0x0000000000000000#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 48) (inst := (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x00#5) 0x0000000000000000#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_52 : (bprog mpl j).fetchMem m (mpl.base 15 + 52#64) =
    some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x0b#5) (AddrMode.UnscaledOffset (Reg.gpr 0x00#5) 0x000000000000000c#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 52) (inst := (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x0b#5) (AddrMode.UnscaledOffset (Reg.gpr 0x00#5) 0x000000000000000c#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_56 : (bprog mpl j).fetchMem m (mpl.base 15 + 56#64) =
    some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x0c#5) (AddrMode.UnscaledOffset (Reg.gpr 0x00#5) 0x0000000000000013#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 56) (inst := (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x0c#5) (AddrMode.UnscaledOffset (Reg.gpr 0x00#5) 0x0000000000000013#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_60 : (bprog mpl j).fetchMem m (mpl.base 15 + 60#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x15#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 60) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x15#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_64 : (bprog mpl j).fetchMem m (mpl.base 15 + 64#64) =
    some (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x00#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 64) (inst := (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x00#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_68 : (bprog mpl j).fetchMem m (mpl.base 15 + 68#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) 3 53) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 68) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) 3 53)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_72 : (bprog mpl j).fetchMem m (mpl.base 15 + 72#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 0x0007ffffffffffff#64) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 72) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 0x0007ffffffffffff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_76 : (bprog mpl j).fetchMem m (mpl.base 15 + 76#64) =
    some (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x14#5) 0x0001#16 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 76) (inst := (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x14#5) 0x0001#16 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_80 : (bprog mpl j).fetchMem m (mpl.base 15 + 80#64) =
    some (Instr.strSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.sp) 0x0000000000000058#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 80) (inst := (Instr.strSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.sp) 0x0000000000000058#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_84 : (bprog mpl j).fetchMem m (mpl.base 15 + 84#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.sp) 0x0000000000000008#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 84) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.sp) 0x0000000000000008#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_88 : (bprog mpl j).fetchMem m (mpl.base 15 + 88#64) =
    some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x09#5) 0x0000000000000018#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 88) (inst := (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x09#5) 0x0000000000000018#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_92 : (bprog mpl j).fetchMem m (mpl.base 15 + 92#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x09#5) (Reg.gpr 0x0b#5) 6 56) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 92) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x09#5) (Reg.gpr 0x0b#5) 6 56)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_96 : (bprog mpl j).fetchMem m (mpl.base 15 + 96#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0b#5) (Reg.gpr 0x0c#5) 1 51) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 96) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0b#5) (Reg.gpr 0x0c#5) 1 51)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_100 : (bprog mpl j).fetchMem m (mpl.base 15 + 100#64) =
    some (Instr.ldrSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.UnscaledOffset (Reg.sp) 0x0000000000000008#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 100) (inst := (Instr.ldrSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.UnscaledOffset (Reg.sp) 0x0000000000000008#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_104 : (bprog mpl j).fetchMem m (mpl.base 15 + 104#64) =
    some (Instr.strSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.sp) 0x0000000000000068#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 104) (inst := (Instr.strSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.sp) 0x0000000000000068#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_108 : (bprog mpl j).fetchMem m (mpl.base 15 + 108#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 12 62) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 108) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 12 62)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_112 : (bprog mpl j).fetchMem m (mpl.base 15 + 112#64) =
    some (Instr.str (MemWidth.X64) (Reg.xzr) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 112) (inst := (Instr.str (MemWidth.X64) (Reg.xzr) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_116 : (bprog mpl j).fetchMem m (mpl.base 15 + 116#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x09#5) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000018#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 116) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x09#5) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000018#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_128 : (bprog mpl j).fetchMem m (mpl.base 15 + 128#64) =
    some (Instr.strSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.Offset (Reg.sp) 0x0000000000000080#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 128) (inst := (Instr.strSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.Offset (Reg.sp) 0x0000000000000080#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_132 : (bprog mpl j).fetchMem m (mpl.base 15 + 132#64) =
    some (Instr.ldpSimd (SimdMemSize.Q128) 0x02#5 0x01#5 (AddrMode.Offset (Reg.gpr 0x09#5) 0x0000000000000000#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 132) (inst := (Instr.ldpSimd (SimdMemSize.Q128) 0x02#5 0x01#5 (AddrMode.Offset (Reg.gpr 0x09#5) 0x0000000000000000#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_136 : (bprog mpl j).fetchMem m (mpl.base 15 + 136#64) =
    some (Instr.ldrSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.sp) 0x0000000000000018#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 136) (inst := (Instr.ldrSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.UnscaledOffset (Reg.sp) 0x0000000000000018#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_140 : (bprog mpl j).fetchMem m (mpl.base 15 + 140#64) =
    some (Instr.str (MemWidth.X64) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x0000000000000028#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 140) (inst := (Instr.str (MemWidth.X64) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x0000000000000028#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_144 : (bprog mpl j).fetchMem m (mpl.base 15 + 144#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.sp) 0x080#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 144) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x09#5) (Reg.sp) 0x080#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_148 : (bprog mpl j).fetchMem m (mpl.base 15 + 148#64) =
    some (Instr.str (MemWidth.X64) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 148) (inst := (Instr.str (MemWidth.X64) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_152 : (bprog mpl j).fetchMem m (mpl.base 15 + 152#64) =
    some (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x08#5) 0x0100#16 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 152) (inst := (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x08#5) 0x0100#16 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_156 : (bprog mpl j).fetchMem m (mpl.base 15 + 156#64) =
    some (Instr.stpSimd (SimdMemSize.Q128) 0x02#5 0x01#5 (AddrMode.Offset (Reg.sp) 0x0000000000000030#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 156) (inst := (Instr.stpSimd (SimdMemSize.Q128) 0x02#5 0x01#5 (AddrMode.Offset (Reg.sp) 0x0000000000000030#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_160 : (bprog mpl j).fetchMem m (mpl.base 15 + 160#64) =
    some (Instr.str (MemWidth.X64) (Reg.xzr) (AddrMode.Offset (Reg.sp) 0x0000000000000078#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 160) (inst := (Instr.str (MemWidth.X64) (Reg.xzr) (AddrMode.Offset (Reg.sp) 0x0000000000000078#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_164 : (bprog mpl j).fetchMem m (mpl.base 15 + 164#64) =
    some (Instr.strSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.Offset (Reg.gpr 0x09#5) 0x0000000000000010#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 164) (inst := (Instr.strSimd (SimdMemSize.Q128) 0x00#5 (AddrMode.Offset (Reg.gpr 0x09#5) 0x0000000000000010#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_168 : (bprog mpl j).fetchMem m (mpl.base 15 + 168#64) =
    some (Instr.str (MemWidth.X64) (Reg.xzr) (AddrMode.Offset (Reg.sp) 0x00000000000000c8#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 168) (inst := (Instr.str (MemWidth.X64) (Reg.xzr) (AddrMode.Offset (Reg.sp) 0x00000000000000c8#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_172 : (bprog mpl j).fetchMem m (mpl.base 15 + 172#64) =
    some (Instr.strSimd (SimdMemSize.Q128) 0x02#5 (AddrMode.UnscaledOffset (Reg.gpr 0x09#5) 0x0000000000000028#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 172) (inst := (Instr.strSimd (SimdMemSize.Q128) 0x02#5 (AddrMode.UnscaledOffset (Reg.gpr 0x09#5) 0x0000000000000028#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_176 : (bprog mpl j).fetchMem m (mpl.base 15 + 176#64) =
    some (Instr.strSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.UnscaledOffset (Reg.gpr 0x09#5) 0x0000000000000038#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 176) (inst := (Instr.strSimd (SimdMemSize.Q128) 0x01#5 (AddrMode.UnscaledOffset (Reg.gpr 0x09#5) 0x0000000000000038#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_180 : (bprog mpl j).fetchMem m (mpl.base 15 + 180#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x01#5) (Reg.xzr) (AddrMode.Offset (Reg.gpr 0x1d#5) 0xffffffffffffffd0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 180) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x01#5) (Reg.xzr) (AddrMode.Offset (Reg.gpr 0x1d#5) 0xffffffffffffffd0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_184 : (bprog mpl j).fetchMem m (mpl.base 15 + 184#64) =
    some (Instr.str (MemWidth.X64) (Reg.gpr 0x08#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffe0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 184) (inst := (Instr.str (MemWidth.X64) (Reg.gpr 0x08#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffe0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_188 : (bprog mpl j).fetchMem m (mpl.base 15 + 188#64) =
    some (Instr.cbz (RegWidth.W64) true (Reg.gpr 0x14#5) 0x0000000000000154#64) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 188) (inst := (Instr.cbz (RegWidth.W64) true (Reg.gpr 0x14#5) 0x0000000000000154#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_192 : (bprog mpl j).fetchMem m (mpl.base 15 + 192#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x1d#5) 0xffffffffffffffd8#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 192) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x1d#5) 0xffffffffffffffd8#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_196 : (bprog mpl j).fetchMem m (mpl.base 15 + 196#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 196) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_200 : (bprog mpl j).fetchMem m (mpl.base 15 + 200#64) =
    some (Instr.bCond (CondCode.CS) 0x0000000000000178#64) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 200) (inst := (Instr.bCond (CondCode.CS) 0x0000000000000178#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_204 : (bprog mpl j).fetchMem m (mpl.base 15 + 204#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x09#5) (Reg.gpr 0x0a#5) 0x001#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 204) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x09#5) (Reg.gpr 0x0a#5) 0x001#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_208 : (bprog mpl j).fetchMem m (mpl.base 15 + 208#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x0a#5) 0x101#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 208) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x0a#5) 0x101#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_212 : (bprog mpl j).fetchMem m (mpl.base 15 + 212#64) =
    some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) 3 63) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 212) (inst := (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) 3 63)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_216 : (bprog mpl j).fetchMem m (mpl.base 15 + 216#64) =
    some (Instr.str (MemWidth.X64) (Reg.gpr 0x09#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffe0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 216) (inst := (Instr.str (MemWidth.X64) (Reg.gpr 0x09#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffe0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_220 : (bprog mpl j).fetchMem m (mpl.base 15 + 220#64) =
    some (Instr.bCond (CondCode.CS) 0x000000000000025c#64) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 220) (inst := (Instr.bCond (CondCode.CS) 0x000000000000025c#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_224 : (bprog mpl j).fetchMem m (mpl.base 15 + 224#64) =
    some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x0a#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffd0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 224) (inst := (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x0a#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffd0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_228 : (bprog mpl j).fetchMem m (mpl.base 15 + 228#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) 0x0000000000000007#64) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 228) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) 0x0000000000000007#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_232 : (bprog mpl j).fetchMem m (mpl.base 15 + 232#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x14#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 232) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x14#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_236 : (bprog mpl j).fetchMem m (mpl.base 15 + 236#64) =
    some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x08#5) (AddrMode.RegOffset (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ExtendType.UXTX) 0)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 236) (inst := (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x08#5) (AddrMode.RegOffset (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ExtendType.UXTX) 0))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_240 : (bprog mpl j).fetchMem m (mpl.base 15 + 240#64) =
    some (Instr.dataProc2 (RegWidth.W32) (DataProc2Op.LSRV) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 240) (inst := (Instr.dataProc2 (RegWidth.W32) (DataProc2Op.LSRV) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_244 : (bprog mpl j).fetchMem m (mpl.base 15 + 244#64) =
    some (Instr.logicalImm (RegWidth.W32) (LogicalOp.AND) (Reg.gpr 0x16#5) (Reg.gpr 0x08#5) 0x0000000100000001#64) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 244) (inst := (Instr.logicalImm (RegWidth.W32) (LogicalOp.AND) (Reg.gpr 0x16#5) (Reg.gpr 0x08#5) 0x0000000100000001#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_248 : (bprog mpl j).fetchMem m (mpl.base 15 + 248#64) =
    some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x00#5) (Reg.gpr 0x16#5) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 248) (inst := (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x00#5) (Reg.gpr 0x16#5) (Reg.gpr 0x00#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_256 : (bprog mpl j).fetchMem m (mpl.base 15 + 256#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x10#5) (Reg.gpr 0x12#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 256) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x10#5) (Reg.gpr 0x12#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_260 : (bprog mpl j).fetchMem m (mpl.base 15 + 260#64) =
    some (Instr.addSubExt (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x0a#5) (Reg.gpr 0x15#5) (Reg.gpr 0x00#5) (ExtendType.UXTB) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 260) (inst := (Instr.addSubExt (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x0a#5) (Reg.gpr 0x15#5) (Reg.gpr 0x00#5) (ExtendType.UXTB) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_264 : (bprog mpl j).fetchMem m (mpl.base 15 + 264#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x08#5) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000080#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 264) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x08#5) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000080#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_268 : (bprog mpl j).fetchMem m (mpl.base 15 + 268#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x00#5) (Reg.gpr 0x05#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 268) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x00#5) (Reg.gpr 0x05#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_272 : (bprog mpl j).fetchMem m (mpl.base 15 + 272#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x06#5) (Reg.gpr 0x07#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 272) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x06#5) (Reg.gpr 0x07#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_276 : (bprog mpl j).fetchMem m (mpl.base 15 + 276#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (Reg.gpr 0x10#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 276) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (Reg.gpr 0x10#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_280 : (bprog mpl j).fetchMem m (mpl.base 15 + 280#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0e#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 280) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0e#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_284 : (bprog mpl j).fetchMem m (mpl.base 15 + 284#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 284) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_288 : (bprog mpl j).fetchMem m (mpl.base 15 + 288#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x09#5) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.sp) 0x0000000000000090#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 288) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x09#5) (Reg.gpr 0x0c#5) (AddrMode.Offset (Reg.sp) 0x0000000000000090#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_292 : (bprog mpl j).fetchMem m (mpl.base 15 + 292#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x11#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 292) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x11#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_296 : (bprog mpl j).fetchMem m (mpl.base 15 + 296#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x18#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x10#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 296) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x18#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x10#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_300 : (bprog mpl j).fetchMem m (mpl.base 15 + 300#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 300) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_304 : (bprog mpl j).fetchMem m (mpl.base 15 + 304#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x19#5) (Reg.gpr 0x11#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 304) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x19#5) (Reg.gpr 0x11#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_308 : (bprog mpl j).fetchMem m (mpl.base 15 + 308#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x17#5) (Reg.gpr 0x03#5) (AddrMode.Offset (Reg.sp) 0x0000000000000060#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 308) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x17#5) (Reg.gpr 0x03#5) (AddrMode.Offset (Reg.sp) 0x0000000000000060#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_312 : (bprog mpl j).fetchMem m (mpl.base 15 + 312#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0f#5) (Reg.gpr 0x09#5) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 312) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0f#5) (Reg.gpr 0x09#5) (Reg.gpr 0x00#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_316 : (bprog mpl j).fetchMem m (mpl.base 15 + 316#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x12#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x05#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 316) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x12#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x05#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_320 : (bprog mpl j).fetchMem m (mpl.base 15 + 320#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x18#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 320) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x18#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_324 : (bprog mpl j).fetchMem m (mpl.base 15 + 324#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0e#5) (Reg.gpr 0x0f#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 324) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0e#5) (Reg.gpr 0x0f#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_328 : (bprog mpl j).fetchMem m (mpl.base 15 + 328#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0f#5) (Reg.gpr 0x10#5) (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 328) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0f#5) (Reg.gpr 0x10#5) (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_332 : (bprog mpl j).fetchMem m (mpl.base 15 + 332#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x1a#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 332) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x1a#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x00#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_336 : (bprog mpl j).fetchMem m (mpl.base 15 + 336#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x02#5) (Reg.gpr 0x12#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 336) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x02#5) (Reg.gpr 0x12#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_340 : (bprog mpl j).fetchMem m (mpl.base 15 + 340#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0b#5) (Reg.gpr 0x11#5) (Reg.gpr 0x0b#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 340) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0b#5) (Reg.gpr 0x11#5) (Reg.gpr 0x0b#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_344 : (bprog mpl j).fetchMem m (mpl.base 15 + 344#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x05#5) (Reg.gpr 0x02#5) (Reg.gpr 0x05#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 344) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x05#5) (Reg.gpr 0x02#5) (Reg.gpr 0x05#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_348 : (bprog mpl j).fetchMem m (mpl.base 15 + 348#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x04#5) (Reg.gpr 0x01#5) (AddrMode.Offset (Reg.sp) 0x0000000000000070#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 348) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x04#5) (Reg.gpr 0x01#5) (AddrMode.Offset (Reg.sp) 0x0000000000000070#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_352 : (bprog mpl j).fetchMem m (mpl.base 15 + 352#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x00#5) (Reg.gpr 0x0f#5) (Reg.gpr 0x06#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 352) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x00#5) (Reg.gpr 0x0f#5) (Reg.gpr 0x06#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_356 : (bprog mpl j).fetchMem m (mpl.base 15 + 356#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x1b#5) (Reg.gpr 0x10#5) (Reg.gpr 0x07#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 356) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x1b#5) (Reg.gpr 0x10#5) (Reg.gpr 0x07#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_360 : (bprog mpl j).fetchMem m (mpl.base 15 + 360#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x1a#5) (Reg.gpr 0x05#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 360) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x1a#5) (Reg.gpr 0x05#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_364 : (bprog mpl j).fetchMem m (mpl.base 15 + 364#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x12#5) (Reg.gpr 0x00#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 364) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x12#5) (Reg.gpr 0x00#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_368 : (bprog mpl j).fetchMem m (mpl.base 15 + 368#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x00#5) (Reg.gpr 0x1c#5) (AddrMode.Offset (Reg.sp) 0x00000000000000b0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 368) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x00#5) (Reg.gpr 0x1c#5) (AddrMode.Offset (Reg.sp) 0x00000000000000b0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_372 : (bprog mpl j).fetchMem m (mpl.base 15 + 372#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x18#5) (Reg.gpr 0x1b#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 372) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x18#5) (Reg.gpr 0x1b#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_376 : (bprog mpl j).fetchMem m (mpl.base 15 + 376#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x06#5) (Reg.gpr 0x12#5) (Reg.gpr 0x06#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 376) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x06#5) (Reg.gpr 0x12#5) (Reg.gpr 0x06#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_380 : (bprog mpl j).fetchMem m (mpl.base 15 + 380#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x08#5) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000080#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 380) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x08#5) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000080#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_384 : (bprog mpl j).fetchMem m (mpl.base 15 + 384#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x07#5) (Reg.gpr 0x18#5) (Reg.gpr 0x07#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 384) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x07#5) (Reg.gpr 0x18#5) (Reg.gpr 0x07#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_388 : (bprog mpl j).fetchMem m (mpl.base 15 + 388#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 388) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_392 : (bprog mpl j).fetchMem m (mpl.base 15 + 392#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x02#5) (Reg.gpr 0x0c#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 392) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x02#5) (Reg.gpr 0x0c#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_396 : (bprog mpl j).fetchMem m (mpl.base 15 + 396#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x19#5) (Reg.gpr 0x1c#5) (Reg.gpr 0x03#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 396) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x19#5) (Reg.gpr 0x1c#5) (Reg.gpr 0x03#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_400 : (bprog mpl j).fetchMem m (mpl.base 15 + 400#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x1e#5) (Reg.gpr 0x00#5) (Reg.gpr 0x17#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 400) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x1e#5) (Reg.gpr 0x00#5) (Reg.gpr 0x17#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_404 : (bprog mpl j).fetchMem m (mpl.base 15 + 404#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x06#5) (Reg.gpr 0x07#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 404) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x06#5) (Reg.gpr 0x07#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_408 : (bprog mpl j).fetchMem m (mpl.base 15 + 408#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x05#5) (Reg.gpr 0x19#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 408) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x05#5) (Reg.gpr 0x19#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_412 : (bprog mpl j).fetchMem m (mpl.base 15 + 412#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x00000000000000c0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 412) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x00000000000000c0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_416 : (bprog mpl j).fetchMem m (mpl.base 15 + 416#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x1b#5) (Reg.gpr 0x1e#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 416) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x1b#5) (Reg.gpr 0x1e#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_420 : (bprog mpl j).fetchMem m (mpl.base 15 + 420#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.sp) 0x0000000000000090#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 420) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.sp) 0x0000000000000090#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_424 : (bprog mpl j).fetchMem m (mpl.base 15 + 424#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x12#5) (Reg.gpr 0x0f#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 424) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x12#5) (Reg.gpr 0x0f#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_428 : (bprog mpl j).fetchMem m (mpl.base 15 + 428#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x18#5) (Reg.gpr 0x10#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 428) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x18#5) (Reg.gpr 0x10#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_432 : (bprog mpl j).fetchMem m (mpl.base 15 + 432#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x17#5) (Reg.gpr 0x1b#5) (Reg.gpr 0x17#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 432) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x17#5) (Reg.gpr 0x1b#5) (Reg.gpr 0x17#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_436 : (bprog mpl j).fetchMem m (mpl.base 15 + 436#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x03#5) (Reg.gpr 0x05#5) (Reg.gpr 0x03#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 436) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x03#5) (Reg.gpr 0x05#5) (Reg.gpr 0x03#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_440 : (bprog mpl j).fetchMem m (mpl.base 15 + 440#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x06#5) (Reg.gpr 0x1a#5) (Reg.gpr 0x04#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 440) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x06#5) (Reg.gpr 0x1a#5) (Reg.gpr 0x04#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_444 : (bprog mpl j).fetchMem m (mpl.base 15 + 444#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x07#5) (Reg.gpr 0x19#5) (Reg.gpr 0x01#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 444) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x07#5) (Reg.gpr 0x19#5) (Reg.gpr 0x01#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_448 : (bprog mpl j).fetchMem m (mpl.base 15 + 448#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 448) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_452 : (bprog mpl j).fetchMem m (mpl.base 15 + 452#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x06#5) (Reg.gpr 0x06#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 452) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x06#5) (Reg.gpr 0x06#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_456 : (bprog mpl j).fetchMem m (mpl.base 15 + 456#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x07#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 456) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x07#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_460 : (bprog mpl j).fetchMem m (mpl.base 15 + 460#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x1b#5) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 460) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x1b#5) (Reg.gpr 0x00#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_464 : (bprog mpl j).fetchMem m (mpl.base 15 + 464#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x04#5) (Reg.gpr 0x06#5) (Reg.gpr 0x04#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 464) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x04#5) (Reg.gpr 0x06#5) (Reg.gpr 0x04#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_468 : (bprog mpl j).fetchMem m (mpl.base 15 + 468#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x01#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x01#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 468) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x01#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x01#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_472 : (bprog mpl j).fetchMem m (mpl.base 15 + 472#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x05#5) (Reg.gpr 0x1c#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 472) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x05#5) (Reg.gpr 0x1c#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_476 : (bprog mpl j).fetchMem m (mpl.base 15 + 476#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x04#5) (Reg.gpr 0x01#5) (AddrMode.Offset (Reg.sp) 0x0000000000000070#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 476) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x04#5) (Reg.gpr 0x01#5) (AddrMode.Offset (Reg.sp) 0x0000000000000070#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_480 : (bprog mpl j).fetchMem m (mpl.base 15 + 480#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x030#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 480) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x030#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_484 : (bprog mpl j).fetchMem m (mpl.base 15 + 484#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.sp) 0x080#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 484) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.sp) 0x080#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_488 : (bprog mpl j).fetchMem m (mpl.base 15 + 488#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.sp) 0x00000000000000b0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 488) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.sp) 0x00000000000000b0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_492 : (bprog mpl j).fetchMem m (mpl.base 15 + 492#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x06#5) (Reg.gpr 0x1a#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 492) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x06#5) (Reg.gpr 0x1a#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_496 : (bprog mpl j).fetchMem m (mpl.base 15 + 496#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x19#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 496) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x19#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_500 : (bprog mpl j).fetchMem m (mpl.base 15 + 500#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x02#5) (Reg.sp) 0x008#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 500) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x02#5) (Reg.sp) 0x008#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_504 : (bprog mpl j).fetchMem m (mpl.base 15 + 504#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x17#5) (Reg.gpr 0x03#5) (AddrMode.Offset (Reg.sp) 0x0000000000000060#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 504) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x17#5) (Reg.gpr 0x03#5) (AddrMode.Offset (Reg.sp) 0x0000000000000060#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_508 : (bprog mpl j).fetchMem m (mpl.base 15 + 508#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.sp) 0x00000000000000c0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 508) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.sp) 0x00000000000000c0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_516 : (bprog mpl j).fetchMem m (mpl.base 15 + 516#64) =
    some (Instr.str (MemWidth.B8) (Reg.gpr 0x16#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffcc#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 516) (inst := (Instr.str (MemWidth.B8) (Reg.gpr 0x16#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffcc#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_520 : (bprog mpl j).fetchMem m (mpl.base 15 + 520#64) =
    some (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x00#5) (Reg.xzr) (Reg.gpr 0x16#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 520) (inst := (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x00#5) (Reg.xzr) (Reg.gpr 0x16#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_524 : (bprog mpl j).fetchMem m (mpl.base 15 + 524#64) =
    some (Instr.cbz (RegWidth.W64) false (Reg.gpr 0x14#5) 0xfffffffffffffeb4#64) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 524) (inst := (Instr.cbz (RegWidth.W64) false (Reg.gpr 0x14#5) 0xfffffffffffffeb4#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_528 : (bprog mpl j).fetchMem m (mpl.base 15 + 528#64) =
    some (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x16#5) (Reg.xzr) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 528) (inst := (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x16#5) (Reg.xzr) (Reg.gpr 0x00#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_532 : (bprog mpl j).fetchMem m (mpl.base 15 + 532#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x00#5) (Reg.gpr 0x1d#5) 0x030#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 532) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x00#5) (Reg.gpr 0x1d#5) 0x030#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_536 : (bprog mpl j).fetchMem m (mpl.base 15 + 536#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x01#5) (Reg.xzr) (Reg.gpr 0x14#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 536) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x01#5) (Reg.xzr) (Reg.gpr 0x14#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_540 : (bprog mpl j).fetchMem m (mpl.base 15 + 540#64) =
    some (Instr.str (MemWidth.X64) (Reg.gpr 0x15#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffe8#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 540) (inst := (Instr.str (MemWidth.X64) (Reg.gpr 0x15#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffe8#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_548 : (bprog mpl j).fetchMem m (mpl.base 15 + 548#64) =
    some (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x08#5) (Reg.xzr) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 548) (inst := (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x08#5) (Reg.xzr) (Reg.gpr 0x00#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_552 : (bprog mpl j).fetchMem m (mpl.base 15 + 552#64) =
    some (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x00#5) (Reg.xzr) (Reg.gpr 0x16#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 552) (inst := (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORR) (Reg.gpr 0x00#5) (Reg.xzr) (Reg.gpr 0x16#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_556 : (bprog mpl j).fetchMem m (mpl.base 15 + 556#64) =
    some (Instr.logicalImm (RegWidth.W32) (LogicalOp.AND) (Reg.gpr 0x16#5) (Reg.gpr 0x08#5) 0x000000ff000000ff#64) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 556) (inst := (Instr.logicalImm (RegWidth.W32) (LogicalOp.AND) (Reg.gpr 0x16#5) (Reg.gpr 0x08#5) 0x000000ff000000ff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_560 : (bprog mpl j).fetchMem m (mpl.base 15 + 560#64) =
    some (Instr.addSubImm (RegWidth.W32) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x16#5) 0x002#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 560) (inst := (Instr.addSubImm (RegWidth.W32) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x16#5) 0x002#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_564 : (bprog mpl j).fetchMem m (mpl.base 15 + 564#64) =
    some (Instr.bCond (CondCode.EQ) 0x000000000000000c#64) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 564) (inst := (Instr.bCond (CondCode.EQ) 0x000000000000000c#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_568 : (bprog mpl j).fetchMem m (mpl.base 15 + 568#64) =
    some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x14#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffe8#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 568) (inst := (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x14#5) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffe8#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_572 : (bprog mpl j).fetchMem m (mpl.base 15 + 572#64) =
    some (Instr.b 0xfffffffffffffebc#64) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 572) (inst := (Instr.b 0xfffffffffffffebc#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_580 : (bprog mpl j).fetchMem m (mpl.base 15 + 580#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0a#5) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 580) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0a#5) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_584 : (bprog mpl j).fetchMem m (mpl.base 15 + 584#64) =
    some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x00#5) 0x00000000000000ff#64) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 584) (inst := (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x00#5) 0x00000000000000ff#64)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_588 : (bprog mpl j).fetchMem m (mpl.base 15 + 588#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x10#5) (Reg.gpr 0x11#5) (AddrMode.Offset (Reg.sp) 0x0000000000000080#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 588) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x10#5) (Reg.gpr 0x11#5) (AddrMode.Offset (Reg.sp) 0x0000000000000080#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_592 : (bprog mpl j).fetchMem m (mpl.base 15 + 592#64) =
    some (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.xzr) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 592) (inst := (Instr.addSubShift (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.xzr) (Reg.gpr 0x09#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_596 : (bprog mpl j).fetchMem m (mpl.base 15 + 596#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0c#5) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 596) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0c#5) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_600 : (bprog mpl j).fetchMem m (mpl.base 15 + 600#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) 0x001#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 600) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) 0x001#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_604 : (bprog mpl j).fetchMem m (mpl.base 15 + 604#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x01#5) (Reg.gpr 0x02#5) (AddrMode.Offset (Reg.sp) 0x0000000000000090#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 604) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x01#5) (Reg.gpr 0x02#5) (AddrMode.Offset (Reg.sp) 0x0000000000000090#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_608 : (bprog mpl j).fetchMem m (mpl.base 15 + 608#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 608) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_612 : (bprog mpl j).fetchMem m (mpl.base 15 + 612#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x10#5) (Reg.gpr 0x10#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 612) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x10#5) (Reg.gpr 0x10#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_616 : (bprog mpl j).fetchMem m (mpl.base 15 + 616#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0b#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 616) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0b#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_620 : (bprog mpl j).fetchMem m (mpl.base 15 + 620#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x11#5) (Reg.gpr 0x11#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 620) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x11#5) (Reg.gpr 0x11#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_624 : (bprog mpl j).fetchMem m (mpl.base 15 + 624#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0a#5) (Reg.gpr 0x10#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 624) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0a#5) (Reg.gpr 0x10#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_628 : (bprog mpl j).fetchMem m (mpl.base 15 + 628#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0d#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 628) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0d#5) (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_632 : (bprog mpl j).fetchMem m (mpl.base 15 + 632#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0b#5) (Reg.gpr 0x11#5) (Reg.gpr 0x0b#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 632) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0b#5) (Reg.gpr 0x11#5) (Reg.gpr 0x0b#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_636 : (bprog mpl j).fetchMem m (mpl.base 15 + 636#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x10#5) (Reg.gpr 0x02#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 636) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x10#5) (Reg.gpr 0x02#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_640 : (bprog mpl j).fetchMem m (mpl.base 15 + 640#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0e#5) (Reg.gpr 0x0f#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 640) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0e#5) (Reg.gpr 0x0f#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_644 : (bprog mpl j).fetchMem m (mpl.base 15 + 644#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0d#5) (Reg.gpr 0x10#5) (Reg.gpr 0x0d#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 644) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0d#5) (Reg.gpr 0x10#5) (Reg.gpr 0x0d#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_648 : (bprog mpl j).fetchMem m (mpl.base 15 + 648#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x11#5) (Reg.gpr 0x10#5) (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 648) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x11#5) (Reg.gpr 0x10#5) (AddrMode.Offset (Reg.sp) 0x00000000000000a0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_652 : (bprog mpl j).fetchMem m (mpl.base 15 + 652#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0c#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 652) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0c#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_656 : (bprog mpl j).fetchMem m (mpl.base 15 + 656#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x01#5) (Reg.gpr 0x01#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 656) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x01#5) (Reg.gpr 0x01#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_660 : (bprog mpl j).fetchMem m (mpl.base 15 + 660#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x0a#5) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 660) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x0a#5) (Reg.gpr 0x0b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_664 : (bprog mpl j).fetchMem m (mpl.base 15 + 664#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0e#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 664) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0e#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_668 : (bprog mpl j).fetchMem m (mpl.base 15 + 668#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0f#5) (Reg.gpr 0x0f#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 668) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0f#5) (Reg.gpr 0x0f#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_672 : (bprog mpl j).fetchMem m (mpl.base 15 + 672#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0c#5) (Reg.gpr 0x01#5) (Reg.gpr 0x0c#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 672) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0c#5) (Reg.gpr 0x01#5) (Reg.gpr 0x0c#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_676 : (bprog mpl j).fetchMem m (mpl.base 15 + 676#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x11#5) (Reg.gpr 0x11#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 676) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x11#5) (Reg.gpr 0x11#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_680 : (bprog mpl j).fetchMem m (mpl.base 15 + 680#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x10#5) (Reg.gpr 0x10#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 680) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x10#5) (Reg.gpr 0x10#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_684 : (bprog mpl j).fetchMem m (mpl.base 15 + 684#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x0c#5) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 684) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x0c#5) (Reg.gpr 0x0d#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_688 : (bprog mpl j).fetchMem m (mpl.base 15 + 688#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0e#5) (Reg.gpr 0x11#5) (Reg.gpr 0x0e#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 688) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0e#5) (Reg.gpr 0x11#5) (Reg.gpr 0x0e#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_692 : (bprog mpl j).fetchMem m (mpl.base 15 + 692#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0f#5) (Reg.gpr 0x10#5) (Reg.gpr 0x0f#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 692) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0f#5) (Reg.gpr 0x10#5) (Reg.gpr 0x0f#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_696 : (bprog mpl j).fetchMem m (mpl.base 15 + 696#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x12#5) (Reg.gpr 0x00#5) (AddrMode.Offset (Reg.sp) 0x0000000000000060#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 696) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x12#5) (Reg.gpr 0x00#5) (AddrMode.Offset (Reg.sp) 0x0000000000000060#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_700 : (bprog mpl j).fetchMem m (mpl.base 15 + 700#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x0e#5) (Reg.gpr 0x0f#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 700) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x0e#5) (Reg.gpr 0x0f#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_704 : (bprog mpl j).fetchMem m (mpl.base 15 + 704#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x01#5) (Reg.gpr 0x02#5) (AddrMode.Offset (Reg.sp) 0x0000000000000070#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 704) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x01#5) (Reg.gpr 0x02#5) (AddrMode.Offset (Reg.sp) 0x0000000000000070#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_708 : (bprog mpl j).fetchMem m (mpl.base 15 + 708#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x11#5) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.sp) 0x00000000000000b0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 708) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x11#5) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.sp) 0x00000000000000b0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_712 : (bprog mpl j).fetchMem m (mpl.base 15 + 712#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x10#5) (Reg.gpr 0x0e#5) (AddrMode.Offset (Reg.sp) 0x00000000000000c0#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 712) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x10#5) (Reg.gpr 0x0e#5) (AddrMode.Offset (Reg.sp) 0x00000000000000c0#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_716 : (bprog mpl j).fetchMem m (mpl.base 15 + 716#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x12#5) (Reg.gpr 0x12#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 716) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x12#5) (Reg.gpr 0x12#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_720 : (bprog mpl j).fetchMem m (mpl.base 15 + 720#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0c#5) (Reg.gpr 0x00#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 720) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0c#5) (Reg.gpr 0x00#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_724 : (bprog mpl j).fetchMem m (mpl.base 15 + 724#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0d#5) (Reg.gpr 0x01#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 724) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0d#5) (Reg.gpr 0x01#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_728 : (bprog mpl j).fetchMem m (mpl.base 15 + 728#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x02#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 728) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x02#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_732 : (bprog mpl j).fetchMem m (mpl.base 15 + 732#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0b#5) (Reg.gpr 0x11#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 732) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0b#5) (Reg.gpr 0x11#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_736 : (bprog mpl j).fetchMem m (mpl.base 15 + 736#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 736) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_740 : (bprog mpl j).fetchMem m (mpl.base 15 + 740#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x030#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 740) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x00#5) (Reg.sp) 0x030#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_744 : (bprog mpl j).fetchMem m (mpl.base 15 + 744#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x10#5) (Reg.gpr 0x10#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 744) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x10#5) (Reg.gpr 0x10#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_748 : (bprog mpl j).fetchMem m (mpl.base 15 + 748#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x08#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 748) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x08#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_752 : (bprog mpl j).fetchMem m (mpl.base 15 + 752#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0b#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 752) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0b#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_756 : (bprog mpl j).fetchMem m (mpl.base 15 + 756#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x0c#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 756) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x0c#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_760 : (bprog mpl j).fetchMem m (mpl.base 15 + 760#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0c#5) (Reg.gpr 0x10#5) (Reg.gpr 0x0d#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 760) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0c#5) (Reg.gpr 0x10#5) (Reg.gpr 0x0d#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_764 : (bprog mpl j).fetchMem m (mpl.base 15 + 764#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 764) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_768 : (bprog mpl j).fetchMem m (mpl.base 15 + 768#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x0b#5) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.sp) 0x0000000000000060#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 768) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x0b#5) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.sp) 0x0000000000000060#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_772 : (bprog mpl j).fetchMem m (mpl.base 15 + 772#64) =
    some (Instr.stp (RegWidth.W64) (Reg.gpr 0x0c#5) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x0000000000000070#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 772) (inst := (Instr.stp (RegWidth.W64) (Reg.gpr 0x0c#5) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x0000000000000070#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_776 : (bprog mpl j).fetchMem m (mpl.base 15 + 776#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.gpr 0x1d#5) 0x034#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 776) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x08#5) (Reg.gpr 0x1d#5) 0x034#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_780 : (bprog mpl j).fetchMem m (mpl.base 15 + 780#64) =
    some (Instr.str (MemWidth.B8) (Reg.xzr) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffcc#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 780) (inst := (Instr.str (MemWidth.B8) (Reg.xzr) (AddrMode.UnscaledOffset (Reg.gpr 0x1d#5) 0xffffffffffffffcc#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_784 : (bprog mpl j).fetchMem m (mpl.base 15 + 784#64) =
    some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x08#5) (Reg.xzr) (Reg.gpr 0x13#5) (ShiftType.LSL) 0) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 784) (inst := (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x08#5) (Reg.xzr) (Reg.gpr 0x13#5) (ShiftType.LSL) 0)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_792 : (bprog mpl j).fetchMem m (mpl.base 15 + 792#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000160#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 792) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000160#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_796 : (bprog mpl j).fetchMem m (mpl.base 15 + 796#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x16#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x0000000000000150#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 796) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x16#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x0000000000000150#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_800 : (bprog mpl j).fetchMem m (mpl.base 15 + 800#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x18#5) (Reg.gpr 0x17#5) (AddrMode.Offset (Reg.sp) 0x0000000000000140#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 800) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x18#5) (Reg.gpr 0x17#5) (AddrMode.Offset (Reg.sp) 0x0000000000000140#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_804 : (bprog mpl j).fetchMem m (mpl.base 15 + 804#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000130#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 804) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000130#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_808 : (bprog mpl j).fetchMem m (mpl.base 15 + 808#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1c#5) (Reg.gpr 0x1b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000120#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 808) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1c#5) (Reg.gpr 0x1b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000120#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_812 : (bprog mpl j).fetchMem m (mpl.base 15 + 812#64) =
    some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.Offset (Reg.sp) 0x0000000000000110#64)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 812) (inst := (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1d#5) (Reg.gpr 0x1e#5) (AddrMode.Offset (Reg.sp) 0x0000000000000110#64))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_816 : (bprog mpl j).fetchMem m (mpl.base 15 + 816#64) =
    some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.sp) (Reg.sp) 0x170#12 false) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 816) (inst := (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.sp) (Reg.sp) 0x170#12 false)) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_820 : (bprog mpl j).fetchMem m (mpl.base 15 + 820#64) =
    some (Instr.ret (Reg.gpr 0x1e#5)) := by
  have := fetch_at' hP hCL (by decide) j blk15 len15 (off := 820) (inst := (Instr.ret (Reg.gpr 0x1e#5))) (by decide) rfl (by decide +kernel) hk
  exact this

theorem c15_252 {j' offj : Nat} (hlk : lookupBlockSym callee15_4 x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 15 + 252#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 15 + BitVec.ofNat 64 252))) :=
  fetch_bl hP hCL (i := 15) (by decide) j (off := 252) (name := callee15_4) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c15_512 {j' offj : Nat} (hlk : lookupBlockSym callee15_3 x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 15 + 512#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 15 + BitVec.ofNat 64 512))) :=
  fetch_bl hP hCL (i := 15) (by decide) j (off := 512) (name := callee15_3) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c15_544 {j' offj : Nat} (hlk : lookupBlockSym callee15_0 x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 15 + 544#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 15 + BitVec.ofNat 64 544))) :=
  fetch_bl hP hCL (i := 15) (by decide) j (off := 544) (name := callee15_0) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c15_576 {j' offj : Nat} (hlk : lookupBlockSym callee15_4 x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 15 + 576#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 15 + BitVec.ofNat 64 576))) :=
  fetch_bl hP hCL (i := 15) (by decide) j (off := 576) (name := callee15_4) (by decide +kernel)
    (by decide +kernel) hlk hk

theorem c15_788 {j' offj : Nat} (hlk : lookupBlockSym callee15_1 x25519CliMultiLib.blocks = some (j', offj)) :
    (bprog mpl j).fetchMem m (mpl.base 15 + 788#64) =
      some (.bl (mpl.base j' + BitVec.ofNat 64 offj - (mpl.base 15 + BitVec.ofNat 64 788))) :=
  fetch_bl hP hCL (i := 15) (by decide) j (off := 788) (name := callee15_1) (by decide +kernel)
    (by decide +kernel) hlk hk

end

end X25519Dalek.LP

end
end

section
section
/-! # Relocated `ADRP`/`ADD` (and their relaxed `NOP`/`ADR` form): loading a `.rodata` address

Decoding lemmas copied from the sibling batch's `Solutions/X25519DalekEdwards/Reloc.lean`, itself from
the zlib CRC-32 mission's `ZlibCrc32.Small.RelocBase`/`RelocTab`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

section words
variable (D : BitVec 64)

theorem wA_maskTab9 : adrpWordOff 0x90000009#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_31Tab9 : (adrpWordOff 0x90000009#32 D).getLsbD 31 = true := by
  simp [adrpWordOff]

theorem wA_rdTab9 : (adrpWordOff 0x90000009#32 D).extractLsb' 0 5 = 9#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_offTab9 (hlo : ∀ i, i < 12 → D.getLsbD i = false)
    (hhi : ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32) :
    ((adrpWordOff 0x90000009#32 D).extractLsb' 5 19 ++
      (adrpWordOff 0x90000009#32 D).extractLsb' 29 2).signExtend 64 <<< 12 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getMsbD]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm

theorem wC_maskTab9 : adrWordOff 0x10000009#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_31Tab9 : (adrWordOff 0x10000009#32 D).getLsbD 31 = false := by
  simp [adrWordOff]

theorem wC_rdTab9 : (adrWordOff 0x10000009#32 D).extractLsb' 0 5 = 9#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_offTab9 (hhi : ∀ i, 20 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 20) :
    ((adrWordOff 0x10000009#32 D).extractLsb' 5 19 ++
      (adrWordOff 0x10000009#32 D).extractLsb' 29 2).signExtend 64 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | rfl | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm

theorem wB_maskTab9 : lo12Word 0 0x91000129#32 D &&& 0x1f800000#32 = 0x11000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wB_bitsTab9 : (lo12Word 0 0x91000129#32 D).getLsbD 31 = true ∧
    (lo12Word 0 0x91000129#32 D).getLsbD 30 = false ∧
    (lo12Word 0 0x91000129#32 D).getLsbD 29 = false ∧
    (lo12Word 0 0x91000129#32 D).getLsbD 22 = false := by
  simp [lo12Word]

theorem wB_rdTab9 : (lo12Word 0 0x91000129#32 D).extractLsb' 0 5 = 9#5 ∧
    (lo12Word 0 0x91000129#32 D).extractLsb' 5 5 = 9#5 := by
  constructor <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem wB_immTab9 : (lo12Word 0 0x91000129#32 D).extractLsb' 10 12 = D.extractLsb' 0 12 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

end words

theorem decode_ATab9 {P T : BitVec 64} (hr : AdrpInRange P T) :
    decode (adrpWord 0x90000009#32 P T) = some (.adr true (.gpr 9#5) (pageOf T - pageOf P)) := by
  rw [adrpWord, decode_adr_class _ (wA_maskTab9 _), wA_31Tab9, wA_rdTab9,
    wA_offTab9 _ (lo_bits T P) (hi_bits32 _ hr.1 hr.2)]
  rfl

theorem decode_CTab9 {P T : BitVec 64} (hr : AdrInRange P T) :
    decode (adrWord (adrTemplate 0x91000129#32) P T) = some (.adr false (.gpr 9#5) (T - P)) := by
  rw [adrWord, show adrTemplate 0x91000129#32 = 0x10000009#32 by decide,
    decode_adr_class _ (wC_maskTab9 _), wC_31Tab9, wC_rdTab9, if_neg (by decide), wC_offTab9 _ (hi_bits20 _ hr.1 hr.2)]
  rfl

theorem decode_BTab9 (T : BitVec 64) :
    decode (lo12Word 0 0x91000129#32 T) =
      some (.addSubImm .W64 .ADD (.gpr 9#5) (.gpr 9#5) (T.extractLsb' 0 12) false) := by
  obtain ⟨b31, b30, b29, b22⟩ := wB_bitsTab9 T
  rw [decode_addimm_class _ (wB_maskTab9 _), b31, b30, b29, b22, wB_rdTab9 T |>.1, wB_rdTab9 T |>.2, wB_immTab9]
  rfl



abbrev symOne : String := "curve25519_dalek:.rodata..Lanon.0"

theorem lookup_A249 : lookupBlockSym symOne x25519CliMultiLib.blocks = none := by decide

theorem resolve_A249 (mpl : MultiPlacement) : x25519CliMultiLib.resolve mpl symOne = mpl.ρ symOne := by
  simp [MultiPlacedLib.resolve, lookup_A249]

theorem target15 (mpl : MultiPlacement) (o : Nat) (k : RelocKind) (sym : String)
    (hlk : lookup sym x25519CliBlk15.symbols = none) :
    x25519CliBlk15.target (x25519CliMultiLib.blockPlacement mpl 15) { off := o, kind := k, sym := sym } =
      x25519CliMultiLib.resolve mpl sym := by
  simp [CodeBlock.target, CodeBlock.resolve, hlk, addSignedAddr, MultiPlacedLib.blockPlacement]

theorem pw15_120 (mpl : MultiPlacement) :
    x25519CliBlk15.patchedWord (x25519CliMultiLib.blockPlacement mpl 15) 120 =
      if mpl.relax 15 120 then nopWord
      else adrpWord 0x90000009#32 (mpl.base 15 + BitVec.ofNat 64 120) (mpl.ρ symOne) := by
  have hr : x25519CliBlk15.relocAt? 120 = some { off := 120, kind := .adrpHi21, sym := symOne } := by
    decide +kernel
  have h1 : x25519CliBlk15.relaxableAt 120 = true := by decide +kernel
  have hw : x25519CliBlk15.wordAt 120 = 0x90000009#32 := by decide +kernel
  have hlk : lookup symOne x25519CliBlk15.symbols = none := by decide +kernel
  have hrel : (x25519CliMultiLib.blockPlacement mpl 15).relax = mpl.relax 15 := rfl
  have hbase : (x25519CliMultiLib.blockPlacement mpl 15).base = mpl.base 15 := rfl
  have h12 : x25519CliBlk15.relaxableAt 116 = false := by decide +kernel
  have hT := target15 mpl 120 .adrpHi21 symOne hlk
  rw [resolve_A249] at hT
  cases h : mpl.relax 15 120 <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h12, hr, hw, hrel, hbase,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, hT,
      patchRelocWord, RelocKind.isGotOrTlsIe]

theorem pw15_124 (mpl : MultiPlacement) :
    x25519CliBlk15.patchedWord (x25519CliMultiLib.blockPlacement mpl 15) 124 =
      if mpl.relax 15 120 then
        adrWord (adrTemplate 0x91000129#32) (mpl.base 15 + BitVec.ofNat 64 124) (mpl.ρ symOne)
      else lo12Word 0 0x91000129#32 (mpl.ρ symOne) := by
  have hr : x25519CliBlk15.relocAt? 124 = some { off := 124, kind := .addLo12, sym := symOne } := by
    decide +kernel
  have h1 : x25519CliBlk15.relaxableAt 120 = true := by decide +kernel
  have h2 : x25519CliBlk15.relaxableAt 124 = false := by decide +kernel
  have hw : x25519CliBlk15.wordAt 124 = 0x91000129#32 := by decide +kernel
  have hlk : lookup symOne x25519CliBlk15.symbols = none := by decide +kernel
  have hrel : (x25519CliMultiLib.blockPlacement mpl 15).relax = mpl.relax 15 := rfl
  have hbase : (x25519CliMultiLib.blockPlacement mpl 15).base = mpl.base 15 := rfl
  have hT := target15 mpl 124 .addLo12 symOne hlk
  rw [resolve_A249] at hT
  cases h : mpl.relax 15 120 <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h2, hr, hw, hrel, hbase,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, hT,
      patchRelocWord, RelocKind.isGotOrTlsIe]

theorem placeable15 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) :
    x25519CliBlk15.Placeable (x25519CliMultiLib.blockPlacement mpl 15) := hP.blocks_ok 15 (by decide)

theorem relocTarget15 (mpl : MultiPlacement) (o : Nat) (k : RelocKind) (sym : String)
    (hlk : lookup sym x25519CliBlk15.symbols = none) :
    x25519CliBlk15.relocTarget (x25519CliMultiLib.blockPlacement mpl 15) o { off := o, kind := k, sym := sym } =
      x25519CliMultiLib.resolve mpl sym := by
  have hb2b : x25519CliBlk15.b2bNext? { off := o, kind := k, sym := sym } = none := by
    simp [CodeBlock.b2bNext?, hlk]
  simp only [CodeBlock.relocTarget, hb2b]
  split <;> simp_all [target15]

theorem range15_120 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) :
    AdrpInRange (mpl.base 15 + BitVec.ofNat 64 120) (mpl.ρ symOne) := by
  have hmem : ({ off := 120, kind := .adrpHi21, sym := symOne } : RelocEntry) ∈ x25519CliBlk15.relocs := by
    decide +kernel
  have h := ((placeable15 hP).relocs_ok _ hmem).2.2
  rw [relocTarget15 mpl 120 .adrpHi21 symOne (by decide +kernel), resolve_A249] at h
  exact h

theorem range15_124 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl)
    (hrel : mpl.relax 15 120 = true) :
    AdrInRange (mpl.base 15 + BitVec.ofNat 64 124) (mpl.ρ symOne) := by
  have h1 : x25519CliBlk15.relaxableAt 120 = true := by decide +kernel
  have hr : x25519CliBlk15.relocAt? (120 + 4) = some { off := 124, kind := .addLo12, sym := symOne } := by
    decide +kernel
  have h := (placeable15 hP).relaxed_ok 120 _ (by simp [CodeBlock.relaxedAt, h1]; exact hrel) hr
  rwa [target15 mpl 124 .addLo12 symOne (by decide +kernel), resolve_A249] at h

section
variable {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
  (hCL : x25519CliMultiLib.CodeLoaded mpl m0) (j : Nat) {m : Memory} (hk : m0.KeepsFrozen m)
include hP hCL hk

theorem f15_120 : (bprog mpl j).fetchMem m (mpl.base 15 + BitVec.ofNat 64 120) =
    decode (if mpl.relax 15 120 then nopWord
      else adrpWord 0x90000009#32 (mpl.base 15 + BitVec.ofNat 64 120) (mpl.ρ symOne)) := by
  have hCL' := libCodeLoaded_keepsFrozen hCL hk 15 (by rw [blocks_length]; decide)
  rw [fetch_word hP (by decide) hCL' (by decide) (by rw [blk15, len15]; decide) _ (hook_none mpl j), blk15,
    pw15_120]

theorem f15_124 : (bprog mpl j).fetchMem m (mpl.base 15 + BitVec.ofNat 64 124) =
    decode (if mpl.relax 15 120 then
        adrWord (adrTemplate 0x91000129#32) (mpl.base 15 + BitVec.ofNat 64 124) (mpl.ρ symOne)
      else lo12Word 0 0x91000129#32 (mpl.ρ symOne)) := by
  have hCL' := libCodeLoaded_keepsFrozen hCL hk 15 (by rw [blocks_length]; decide)
  rw [fetch_word hP (by decide) hCL' (by decide) (by rw [blk15, len15]; decide) _ (hook_none mpl j), blk15,
    pw15_124]

end

/-- Offsets 120 and 124 (`adrp x0` / `add x0` of `fe51_one` into `x9`, or their relaxed `nop` / `adr`). -/
theorem pair15 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {j : Nat} {s0 : State} {r : BitVec 5 → BitVec 64}
    {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}
    (hk : m0.KeepsFrozen m) (hrun : s0.status = .Running)
    (h : Reach (bprog mpl j) (mkS s0 (mpl.base 15 + BitVec.ofNat 64 128) (upd r 9#5 (mpl.ρ symOne)) sp ps m v) Q) :
    Reach (bprog mpl j) (mkS s0 (mpl.base 15 + BitVec.ofNat 64 120) r sp ps m v) Q := by
  have hf1 := f15_120 hP hCL j hk
  have hf2 := f15_124 hP hCL j hk
  cases hrel : mpl.relax 15 120
  · simp only [hrel, Bool.false_eq_true, if_false] at hf1 hf2
    rw [decode_ATab9 (range15_120 hP)] at hf1
    rw [decode_BTab9] at hf2
    refine Reach.mk hrun hf1 ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel']
    refine Reach.mk hrun hf2 ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel']
    have e1 : (mpl.base 15 + 120#64 &&& 18446744073709547520#64) = pageOf (mpl.base 15 + 120#64) := rfl
    have e2 : ∀ a b : BitVec 64, a + (b - a) = b := by intro a b; bv_omega
    have e3 : upd (upd r 9#5 (pageOf (mpl.ρ symOne))) 9#5 (pageOf (mpl.ρ symOne) +
        BitVec.zeroExtend 64 (BitVec.extractLsb' 0 12 (mpl.ρ symOne))) = upd r 9#5 (mpl.ρ symOne) := by
      funext k; simp only [upd]; split_ifs
      · exact page_add_lo _
      · rfl
    rw [e1, e2, e3]; exact h
  · simp only [hrel, if_true] at hf1 hf2
    rw [decode_nop] at hf1
    rw [decode_CTab9 (range15_124 hP hrel)] at hf2
    refine Reach.mk hrun hf1 ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel']
    refine Reach.mk hrun hf2 ?_
    simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel']
    exact h

end X25519Dalek.LP

end
end

section
section
/-! # Calls to `mul` and `pow2k` with operands held as 64-bit word lists

The callee contracts speak of byte slices; a caller that keeps its field elements as five-word
lists (`a ↦₆₄* A`) calls through these lemmas, which do the conversion once. After the return the
register file is `csMerge r sf.regs.regs`: the callee-saved registers as before the call, the others
as the callee left them. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 Arm64.Obj

/-- Callee-saved registers (`x19`–`x29`) from `r`, the rest from `rf`. -/
def csMerge (r rf : BitVec 5 → BitVec 64) : BitVec 5 → BitVec 64 :=
  fun k => if 19 ≤ k.toNat ∧ k.toNat ≤ 29 then r k else rf k

theorem csMerge_eq {sf : State} {r : BitVec 5 → BitVec 64} (h : CSRegs sf r) :
    csMerge r sf.regs.regs = sf.regs.regs := by
  funext k
  unfold csMerge
  split_ifs with hk
  · obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29⟩ := h
    have e : k = BitVec.ofNat 5 k.toNat := by simp
    generalize hj : k.toNat = j at e hk
    subst e
    obtain ⟨h1, h2⟩ := hk
    interval_cases j
    all_goals first | exact c19.symm | exact c20.symm | exact c21.symm | exact c22.symm | exact c23.symm | exact c24.symm | exact c25.symm | exact c26.symm | exact c27.symm | exact c28.symm | exact c29.symm
  · rfl

/-- `bl` to the entry of block `j`. -/
theorem y_bl {p : Program} {s0 : State} {pc T : BitVec 64} {r : BitVec 5 → BitVec 64} {sp : BitVec 64}
    {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128} {Q : State → Prop}
    (hrun : s0.status = .Running) (hf : p.fetchMem m pc = some (.bl (T - pc)))
    (h : Reach p (mkS s0 T (upd r 30#5 (pc + 4#64)) sp ps m v) Q) :
    Reach p (mkS s0 pc r sp ps m v) Q := by
  refine Reach.mk hrun hf ?_
  simp only [execInstWithSvc, execAddSubImm, execAddSubShift, execAddSubExt, execLogicalImm, execLogicalShift, execMoveWide, execBitfield, execCondSelect, execDataProc2, execDataProc3, execLdr, execStr, execLdp, execStp, State.readReg, State.writeReg, State.readReg32, evalAddSub, evalLogical, evalBitfield, shiftVal, shift64, shift32, extendVal, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode, Memory.readSized, Memory.writeSized, Memory.readSimdSized, Memory.writeSimdSized, Memory.read128, Memory.write128, MemWidth.bytes, SimdMemSize.bytes, mkS_readSp, mkS_writeSp, mkS_readGpr, mkS_writeGpr, mkS_readXzr, mkS_writeXzr, mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, mkS_mem, mkS_spAligned, mkS_readV, mkS_writeV, mkS_pc, upd_apply, awc_true_fst, awc_false_fst, add_not_add_one, pc_add, zext12_lit, zext16_lit, ConditionHolds, Bool.false_eq_true, Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and, Bool.and_self, ite_true, ite_false, BitVec.add_zero, ↓reduceIte, Reg.lr, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceAdd, beq_self_eq_true, reduceCtorEq, Nat.reduceBEq, Nat.reduceBNe, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or, decide_false, decide_true, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff, Nat.reduceShiftLeft, Nat.reducePow, Nat.shiftLeft_eq, ge_iff_le, gt_iff_lt, and_false, and_true, false_and, true_and, BitVec.ushiftRight_zero, BitVec.shiftLeft_zero, bf_beq_1, bf_beq_2, bf_beq_3, bf_beq_4, bf_beq_5, bf_beq_6, extract_lo128, extract_hi128, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceAppend, BitVec.reduceToNat, BitVec.reduceOfNat, BitVec.reduceZeroExtend, BitVec.reduceGetLsb, add_sub_cancel', sub_add_cancel', BitVec.add_sub_cancel]
  exact h

theorem cs_of_upd30 {sf : State} {r : BitVec 5 → BitVec 64} {x : BitVec 64}
    (h : CSRegs sf (upd r 30#5 x)) : CSRegs sf r := by
  simpa only [CSRegs, upd_apply, BitVec.reduceEq, ite_false] using h

end X25519Dalek.LP

end
end

section
section
/-! # `FieldElement51` buffers: limbs, words, values -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64

theorem cat8_eq_or (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 =
      0#64 ||| b0.zeroExtend 64 <<< 0 ||| b1.zeroExtend 64 <<< 8 ||| b2.zeroExtend 64 <<< 16 |||
      b3.zeroExtend 64 <<< 24 ||| b4.zeroExtend 64 <<< 32 ||| b5.zeroExtend 64 <<< 40 |||
      b6.zeroExtend 64 <<< 48 ||| b7.zeroExtend 64 <<< 56 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  interval_cases i <;> simp only [BitVec.getLsbD_append] <;> simp

theorem readLE8_eq (bs : List (BitVec 8)) (off : Nat) :
    ByteSlice.readLE bs off 8 =
      bs.getD (off + 7) 0 ++ bs.getD (off + 6) 0 ++ bs.getD (off + 5) 0 ++ bs.getD (off + 4) 0 ++
      bs.getD (off + 3) 0 ++ bs.getD (off + 2) 0 ++ bs.getD (off + 1) 0 ++ bs.getD (off + 0) 0 := by
  rw [cat8_eq_or]
  simp only [ByteSlice.readLE, Nat.reduceMul, Nat.add_zero]
  rfl

theorem pack64_drop_take (bs : List (BitVec 8)) (off : Nat) :
    pack64 ((bs.drop off).take 8) = ByteSlice.readLE bs off 8 := by
  rw [readLE8_eq]
  simp only [pack64, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  simp

theorem readLE_drop (bs : List (BitVec 8)) (k off : Nat) :
    ByteSlice.readLE (bs.drop k) off 8 = ByteSlice.readLE bs (k + off) 8 := by
  rw [readLE8_eq, readLE8_eq]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_assoc]

theorem chunks64_getElem : ∀ (k : Nat) (bs : List (BitVec 8)) (i : Nat) (hi : i < (chunks64 bs k).length),
    (chunks64 bs k)[i] = ByteSlice.readLE bs (8 * i) 8
  | 0, _, i, hi => by simp [chunks64] at hi
  | k + 1, bs, 0, _ => by
    simp only [chunks64, List.getElem_cons_zero]
    rw [← pack64_drop_take]; rfl
  | k + 1, bs, i + 1, hi => by
    rw [chunks64_length] at hi
    simp only [chunks64, List.getElem_cons_succ]
    rw [chunks64_getElem k (bs.drop 8) i (by rw [chunks64_length]; omega), readLE_drop]
    congr 1; omega

theorem readLE_take (bs : List (BitVec 8)) (n off : Nat) (h : off + 8 ≤ n) :
    ByteSlice.readLE (bs.take n) off 8 = ByteSlice.readLE bs off 8 := by
  rw [readLE8_eq, readLE8_eq]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  repeat rw [if_pos (by omega)]

/-! ## Field arithmetic -/

theorem readLE_append_left (a b : List (BitVec 8)) (off : Nat) (h : off + 8 ≤ a.length) :
    ByteSlice.readLE (a ++ b) off 8 = ByteSlice.readLE a off 8 := by
  rw [← readLE_take (a ++ b) a.length off h, List.take_left]

theorem readLE_append_right (a b : List (BitVec 8)) (off : Nat) :
    ByteSlice.readLE (a ++ b) (a.length + off) 8 = ByteSlice.readLE b off 8 := by
  rw [← readLE_drop, List.drop_left]

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

theorem list5 {α : Type} (l : List α) (h : l.length = 5) : ∃ a b c d e, l = [a, b, c, d, e] := by
  match l, h with
  | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩

end X25519Dalek.LP

namespace X25519Dalek.LP
open Arm64

end X25519Dalek.LP

namespace X25519Dalek.LP

end X25519Dalek.LP

namespace X25519Dalek.LP

end X25519Dalek.LP

end
end

section
section
/-! # `FieldElement51` add, subtract (with bias) and weak reduction: bounds and values mod p

Ported from google-deepmind/code-verification @ 8c8d371f (Apache-2.0),
`LibsignalBinary/Proofs/HookDischarge/CryptoX25519/Shared51/SliceBase.lean` (lines 156-432),
unchanged except for the namespace. -/

set_option autoImplicit false

namespace X25519Dalek.LP

open Arm64 hiding fpAdd fpSub fpMul fpNeg


end X25519Dalek.LP

end
end

section
section
/-! # `FieldElement51` buffers held as five 64-bit words

`fe51LimbsBounded` and `fe51ValOfBytes` of `[w0, …, w4].flatMap unpack64` in terms of the words. -/

set_option autoImplicit false

namespace X25519Dalek.LP

open Arm64 hiding fpAdd fpSub fpMul fpNeg

theorem pack64_unpack64 (w : BitVec 64) : pack64 (unpack64 w) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack64, unpack64, List.getD_cons_zero, List.getD_cons_succ, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

theorem chunks64_flatMap : ∀ (ws : List (BitVec 64)), chunks64 (ws.flatMap unpack64) ws.length = ws
  | [] => rfl
  | w :: ws => by
    simp only [List.flatMap_cons, List.length_cons, chunks64]
    rw [List.take_left' (unpack64_length w), List.drop_left' (unpack64_length w), pack64_unpack64,
      chunks64_flatMap ws]

theorem readLE_words (ws : List (BitVec 64)) (i : Nat) (hi : i < ws.length) :
    ByteSlice.readLE (ws.flatMap unpack64) (8 * i) 8 = ws[i] := by
  have h := chunks64_getElem ws.length (ws.flatMap unpack64) i (by rw [chunks64_length]; exact hi)
  rw [← h]
  congr 1
  · exact chunks64_flatMap ws

theorem lbw (w0 w1 w2 w3 w4 : BitVec 64) (B : Nat) :
    fe51LimbsBounded ([w0, w1, w2, w3, w4].flatMap unpack64) B ↔
      (w0.toNat < B ∧ w1.toNat < B ∧ w2.toNat < B ∧ w3.toNat < B ∧ w4.toNat < B) := by
  have e0 := readLE_words [w0, w1, w2, w3, w4] 0 (by simp)
  have e1 := readLE_words [w0, w1, w2, w3, w4] 1 (by simp)
  have e2 := readLE_words [w0, w1, w2, w3, w4] 2 (by simp)
  have e3 := readLE_words [w0, w1, w2, w3, w4] 3 (by simp)
  have e4 := readLE_words [w0, w1, w2, w3, w4] 4 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1 e2 e3 e4
  unfold fe51LimbsBounded
  rw [e0, e1, e2, e3, e4]
  simp

theorem valw (w0 w1 w2 w3 w4 : BitVec 64) :
    fe51ValOfBytes ([w0, w1, w2, w3, w4].flatMap unpack64) = fe51Val w0 w1 w2 w3 w4 := by
  have e0 := readLE_words [w0, w1, w2, w3, w4] 0 (by simp)
  have e1 := readLE_words [w0, w1, w2, w3, w4] 1 (by simp)
  have e2 := readLE_words [w0, w1, w2, w3, w4] 2 (by simp)
  have e3 := readLE_words [w0, w1, w2, w3, w4] 3 (by simp)
  have e4 := readLE_words [w0, w1, w2, w3, w4] 4 (by simp)
  simp only [Nat.reduceMul, List.getElem_cons_zero, List.getElem_cons_succ] at e0 e1 e2 e3 e4
  unfold fe51ValOfBytes
  rw [e0, e1, e2, e3, e4]

end X25519Dalek.LP

end
end

section
section
/-! # `MontgomeryPoint * Scalar` (block 15): pure facts

Byte reads at unaligned offsets, the `u`-coordinate decoding into five limbs, the scalar bit the loop
extracts, the constant-time swap and select word identities, and one step of the ladder.
After DeepMind's `Shared51/MontgomeryLadderCode.lean` (google-deepmind/code-verification @ 8c8d371f). -/

set_option autoImplicit false

namespace X25519Dalek.LP

open Arm64 hiding fpAdd fpSub fpMul fpNeg

/-! ## Unaligned reads from a byte slice -/

theorem bytes_read64 {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ₛ bs) ∗ F) (k : Nat) (hk : k + 8 ≤ bs.length) :
    m.read64 (a + BitVec.ofNat 64 k) = ByteSlice.readLE bs k 8 ∧
      m.canRead (a + BitVec.ofNat 64 k) 8 = true := by
  refine ⟨?_, (sat_bytes_access hs k 8 hk).1⟩
  have e : ∀ i, a + BitVec.ofNat 64 k + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (k + i) := by
    intro i; rw [BitVec.add_assoc, BitVec.ofNat_add]
  have g : ∀ i, i < 8 → m.read8 (a + BitVec.ofNat 64 k + BitVec.ofNat 64 i) = bs.getD (k + i) 0 := by
    intro i hi
    rw [e, (sat_bytes_read hs (k + i) (by omega)).1, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega)
  have g3 := g 3 (by omega); have g4 := g 4 (by omega); have g5 := g 5 (by omega)
  have g6 := g 6 (by omega); have g7 := g 7 (by omega)
  simp only [BitVec.ofNat_eq_ofNat] at g0 g1 g2 g3 g4 g5 g6 g7
  rw [readLE8_eq]
  simp only [Memory.read64]
  rw [g0, g1, g2, g3, g4, g5, g6, g7]
  rfl

/-! ## Little-endian values -/

theorem bv64_toNat_bytes (v : BitVec 64) :
    v.toNat = (v.extractLsb' 0 8).toNat + (v.extractLsb' 8 8).toNat * 256 +
      (v.extractLsb' 16 8).toNat * 65536 + (v.extractLsb' 24 8).toNat * 16777216 +
      (v.extractLsb' 32 8).toNat * 4294967296 + (v.extractLsb' 40 8).toNat * 1099511627776 +
      (v.extractLsb' 48 8).toNat * 281474976710656 + (v.extractLsb' 56 8).toNat * 72057594037927936 := by
  have h (k : Nat) : (v.extractLsb' k 8).toNat = (v.toNat / 2 ^ k) % 256 := by
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [h 0, h 8, h 16, h 24, h 32, h 40, h 48, h 56]; have := v.isLt; omega

theorem readLE8_toNat (bs : List (BitVec 8)) (k : Nat) (hk : k + 8 ≤ bs.length) :
    (ByteSlice.readLE bs k 8).toNat =
      (bs.getD k 0#8).toNat + (bs.getD (k + 1) 0#8).toNat * 256 + (bs.getD (k + 2) 0#8).toNat * 65536 +
      (bs.getD (k + 3) 0#8).toNat * 16777216 + (bs.getD (k + 4) 0#8).toNat * 4294967296 +
      (bs.getD (k + 5) 0#8).toNat * 1099511627776 + (bs.getD (k + 6) 0#8).toNat * 281474976710656 +
      (bs.getD (k + 7) 0#8).toNat * 72057594037927936 := by
  have hl : ((bs.drop k).take 8).length = 8 := by simp; omega
  have hu := unpack64_pack64 _ hl
  rw [pack64_drop_take] at hu
  have hv := bv64_toNat_bytes (ByteSlice.readLE bs k 8)
  have gi : ∀ i, i < 8 → ((bs.drop k).take 8).getD i 0 = bs.getD (k + i) 0 := by
    intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    simp [hi]
  simp only [unpack64] at hu
  have e : ∀ i, (hi : i < 8) → (ByteSlice.readLE bs k 8).extractLsb' (8 * i) 8 = bs.getD (k + i) 0 := by
    intro i hi
    rw [← gi i hi, ← hu]
    interval_cases i <;> rfl
  have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega)
  have e3 := e 3 (by omega); have e4 := e 4 (by omega); have e5 := e 5 (by omega)
  have e6 := e 6 (by omega); have e7 := e 7 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul] at e0 e1 e2 e3 e4 e5 e6 e7
  rw [hv, e0, e1, e2, e3, e4, e5, e6, e7]
  rfl

theorem leBytesToNat_take_succ (bs : List (BitVec 8)) :
    ∀ k, k < bs.length →
      leBytesToNat (bs.take (k + 1)) = leBytesToNat (bs.take k) + (bs.getD k 0#8).toNat * 256 ^ k
  | 0, hk => by rcases bs with _ | ⟨b, bs⟩ <;> simp [leBytesToNat] at hk ⊢
  | k + 1, hk => by
    rcases bs with _ | ⟨b, bs⟩
    · simp at hk
    · have ih := leBytesToNat_take_succ bs k (by simpa using hk)
      simp only [List.take_succ_cons, leBytesToNat, List.foldr_cons, List.getD_cons_succ] at ih ⊢
      rw [ih, Nat.pow_succ, ← Nat.mul_assoc]; omega

theorem leBytesToNat_32 (bs : List (BitVec 8)) (hbs : bs.length = 32) :
    leBytesToNat bs =
      (bs.getD 0 0#8).toNat + (bs.getD 1 0#8).toNat * 256 ^ 1 +
      (bs.getD 2 0#8).toNat * 256 ^ 2 + (bs.getD 3 0#8).toNat * 256 ^ 3 +
      (bs.getD 4 0#8).toNat * 256 ^ 4 + (bs.getD 5 0#8).toNat * 256 ^ 5 +
      (bs.getD 6 0#8).toNat * 256 ^ 6 + (bs.getD 7 0#8).toNat * 256 ^ 7 +
      (bs.getD 8 0#8).toNat * 256 ^ 8 + (bs.getD 9 0#8).toNat * 256 ^ 9 +
      (bs.getD 10 0#8).toNat * 256 ^ 10 + (bs.getD 11 0#8).toNat * 256 ^ 11 +
      (bs.getD 12 0#8).toNat * 256 ^ 12 + (bs.getD 13 0#8).toNat * 256 ^ 13 +
      (bs.getD 14 0#8).toNat * 256 ^ 14 + (bs.getD 15 0#8).toNat * 256 ^ 15 +
      (bs.getD 16 0#8).toNat * 256 ^ 16 + (bs.getD 17 0#8).toNat * 256 ^ 17 +
      (bs.getD 18 0#8).toNat * 256 ^ 18 + (bs.getD 19 0#8).toNat * 256 ^ 19 +
      (bs.getD 20 0#8).toNat * 256 ^ 20 + (bs.getD 21 0#8).toNat * 256 ^ 21 +
      (bs.getD 22 0#8).toNat * 256 ^ 22 + (bs.getD 23 0#8).toNat * 256 ^ 23 +
      (bs.getD 24 0#8).toNat * 256 ^ 24 + (bs.getD 25 0#8).toNat * 256 ^ 25 +
      (bs.getD 26 0#8).toNat * 256 ^ 26 + (bs.getD 27 0#8).toNat * 256 ^ 27 +
      (bs.getD 28 0#8).toNat * 256 ^ 28 + (bs.getD 29 0#8).toNat * 256 ^ 29 +
      (bs.getD 30 0#8).toNat * 256 ^ 30 + (bs.getD 31 0#8).toNat * 256 ^ 31 := by
  have htake : bs = bs.take 32 := (List.take_of_length_le (by omega)).symm
  conv => lhs; rw [htake]
  repeat rw [leBytesToNat_take_succ bs _ (by omega)]
  have h0 : leBytesToNat (bs.take 0) = 0 := rfl
  rw [h0]; omega

theorem bv64_mask51_toNat (v : BitVec 64) :
    (v &&& 2251799813685247#64).toNat = v.toNat % 2 ^ 51 := by
  rw [BitVec.toNat_and, show (2251799813685247#64).toNat = 2 ^ 51 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]

/-- The five limbs the code computes from the 32 bytes of `u` (offsets 0, 6, 12, 19, 24). -/
theorem decode_limbs (bs : List (BitVec 8)) (hbs : bs.length = 32) :
    (ByteSlice.readLE bs 0 8 &&& 2251799813685247#64).toNat < 2 ^ 51 ∧
    ((ByteSlice.readLE bs 6 8 >>> 3) &&& 2251799813685247#64).toNat < 2 ^ 51 ∧
    ((ByteSlice.readLE bs 12 8 >>> 6) &&& 2251799813685247#64).toNat < 2 ^ 51 ∧
    ((ByteSlice.readLE bs 19 8 >>> 1) &&& 2251799813685247#64).toNat < 2 ^ 51 ∧
    ((ByteSlice.readLE bs 24 8 >>> 12) &&& 2251799813685247#64).toNat < 2 ^ 51 ∧
    fe51Val (ByteSlice.readLE bs 0 8 &&& 2251799813685247#64)
      ((ByteSlice.readLE bs 6 8 >>> 3) &&& 2251799813685247#64)
      ((ByteSlice.readLE bs 12 8 >>> 6) &&& 2251799813685247#64)
      ((ByteSlice.readLE bs 19 8 >>> 1) &&& 2251799813685247#64)
      ((ByteSlice.readLE bs 24 8 >>> 12) &&& 2251799813685247#64) = decodeU255 bs := by
  have hle32 := leBytesToNat_32 bs hbs
  have hdec : decodeU255 bs = leBytesToNat bs % 2 ^ 255 := by
    unfold decodeU255; rw [List.take_of_length_le (by omega)]
  rw [bv64_mask51_toNat, bv64_mask51_toNat, bv64_mask51_toNat, bv64_mask51_toNat, bv64_mask51_toNat]
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [readLE8_toNat bs 0 (by omega), readLE8_toNat bs 6 (by omega), readLE8_toNat bs 12 (by omega),
    readLE8_toNat bs 19 (by omega), readLE8_toNat bs 24 (by omega)]
  unfold fe51Val
  rw [bv64_mask51_toNat, bv64_mask51_toNat, bv64_mask51_toNat, bv64_mask51_toNat, bv64_mask51_toNat]
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [readLE8_toNat bs 0 (by omega), readLE8_toNat bs 6 (by omega), readLE8_toNat bs 12 (by omega),
    readLE8_toNat bs 19 (by omega), readLE8_toNat bs 24 (by omega)]
  simp only [Nat.reduceAdd] at *
  simp only [Nat.reducePow] at hle32 ⊢
  have := (bs.getD 0 0#8).isLt; have := (bs.getD 1 0#8).isLt; have := (bs.getD 2 0#8).isLt; have := (bs.getD 3 0#8).isLt
  have := (bs.getD 4 0#8).isLt; have := (bs.getD 5 0#8).isLt; have := (bs.getD 6 0#8).isLt; have := (bs.getD 7 0#8).isLt
  have := (bs.getD 8 0#8).isLt; have := (bs.getD 9 0#8).isLt; have := (bs.getD 10 0#8).isLt; have := (bs.getD 11 0#8).isLt
  have := (bs.getD 12 0#8).isLt; have := (bs.getD 13 0#8).isLt; have := (bs.getD 14 0#8).isLt; have := (bs.getD 15 0#8).isLt
  have := (bs.getD 16 0#8).isLt; have := (bs.getD 17 0#8).isLt; have := (bs.getD 18 0#8).isLt; have := (bs.getD 19 0#8).isLt
  have := (bs.getD 20 0#8).isLt; have := (bs.getD 21 0#8).isLt; have := (bs.getD 22 0#8).isLt; have := (bs.getD 23 0#8).isLt
  have := (bs.getD 24 0#8).isLt; have := (bs.getD 25 0#8).isLt; have := (bs.getD 26 0#8).isLt; have := (bs.getD 27 0#8).isLt
  have := (bs.getD 28 0#8).isLt; have := (bs.getD 29 0#8).isLt; have := (bs.getD 30 0#8).isLt; have := (bs.getD 31 0#8).isLt
  rw [hdec]
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩; omega

/-! ## Scalar bits -/

theorem leBytesToNat_div_byte :
    ∀ (bs : List (BitVec 8)) (j : Nat),
      (leBytesToNat bs / 256 ^ j) % 256 = (bs.getD j 0#8).toNat
  | [], j => by simp [leBytesToNat]
  | b :: bs, 0 => by
    simp only [leBytesToNat, List.foldr_cons, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
    have hb := b.isLt; omega
  | b :: bs, j + 1 => by
    have ih := leBytesToNat_div_byte bs j
    simp only [leBytesToNat, List.foldr_cons, List.getD_cons_succ] at ih ⊢
    have hb := b.isLt
    generalize List.foldr (fun (b : BitVec 8) acc => acc * 256 + b.toNat) 0 bs = A at ih ⊢
    have hdiv : (A * 256 + b.toNat) / 256 ^ (j + 1) = A / 256 ^ j := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ j) 256, ← Nat.div_div_eq_div_mul,
          show (A * 256 + b.toNat) / 256 = A by omega]
    rw [hdiv, ih]

theorem mod256_div_pow2_mod2 (N r : Nat) (hr : r < 8) :
    ((N % 256) / 2 ^ r) % 2 = (N / 2 ^ r) % 2 := by
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- Bit `k` of the little-endian value of `bs`. -/
theorem scalar_bit (bs : List (BitVec 8)) (k : Nat) :
    ((bs.getD (k / 8) 0#8).toNat / 2 ^ (k % 8)) % 2 = (leBytesToNat bs / 2 ^ k) % 2 := by
  have hpow : 2 ^ k = 256 ^ (k / 8) * 2 ^ (k % 8) := by
    conv => lhs; rw [show k = 8 * (k / 8) + k % 8 by omega]
    rw [Nat.pow_add, Nat.pow_mul, show 2 ^ 8 = 256 from rfl]
  rw [← leBytesToNat_div_byte bs (k / 8), mod256_div_pow2_mod2 _ (k % 8) (by omega),
      hpow, ← Nat.div_div_eq_div_mul]

/-! ## Constant-time swap and select -/

theorem xor_cswap_left (wa wb : BitVec 64) (s : BitVec 8) (hs : s = 0#8 ∨ s = 1#8) :
    ((wb ^^^ wa) &&& (0#64 - BitVec.setWidth 64 s)) ^^^ wa = if s = 1#8 then wb else wa := by
  rcases hs with rfl | rfl
  · simp
  · simp only [if_true]
    have : (0#64 - BitVec.setWidth 64 1#8) = BitVec.allOnes 64 := by decide
    rw [this, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem xor_cswap_right (wa wb : BitVec 64) (s : BitVec 8) (hs : s = 0#8 ∨ s = 1#8) :
    ((wb ^^^ wa) &&& (0#64 - BitVec.setWidth 64 s)) ^^^ wb = if s = 1#8 then wa else wb := by
  rcases hs with rfl | rfl
  · simp
  · simp only [if_true]
    have : (0#64 - BitVec.setWidth 64 1#8) = BitVec.allOnes 64 := by decide
    rw [this, BitVec.and_allOnes, BitVec.xor_comm wb wa, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero]

/-! ## One step of the ladder -/

theorem montLadderLoop_step_eq (idx k u1 : Nat) (x0 x1 : MontProjPoint)
    (cur : Nat) (hcur_eq : cur = (k / 2 ^ idx) % 2)
    (p0 p1 q0 q1 : MontProjPoint)
    (hp : (p0, p1) = if cur = 1 then (x1, x0) else (x0, x1))
    (hq0 : q0 = (montDiffAddAndDouble u1 p0 p1).1)
    (hq1 : q1 = (montDiffAddAndDouble u1 p0 p1).2) :
    montLadderLoop (idx + 1) k u1 x0 x1 =
      montLadderLoop idx k u1 (if cur = 1 then q1 else q0) (if cur = 1 then q0 else q1) := by
  have hcur : cur < 2 := by rw [hcur_eq]; omega
  rcases (show cur = 0 ∨ cur = 1 by omega) with rfl | rfl
  · simp only [Nat.zero_ne_one, if_false] at hp ⊢
    conv => lhs; unfold montLadderLoop
    rw [← hcur_eq]
    simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
    rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
    subst hq0 hq1; rfl
  · simp only [if_true] at hp ⊢
    conv => lhs; unfold montLadderLoop
    rw [← hcur_eq]
    simp only [BEq.rfl, ↓reduceIte]
    rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
    subst hq0 hq1; rfl

/-! ## Ten-word points (copied from `D12Aux`) -/

theorem pw_list10 {α : Type} (l : List α) (h : l.length = 10) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9, l = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] := by
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9], _ => exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, rfl⟩

theorem pw_flat10 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) :
    [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9].flatMap unpack64 =
      [w0, w1, w2, w3, w4].flatMap unpack64 ++ [w5, w6, w7, w8, w9].flatMap unpack64 := by
  simp [List.flatMap_cons]

theorem pw_readLE_words10 (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) (off : Nat) (h : off < 5) :
    ByteSlice.readLE ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9].flatMap unpack64) (40 + 8 * off) 8 =
      ByteSlice.readLE ([w5, w6, w7, w8, w9].flatMap unpack64) (8 * off) 8 := by
  rw [pw_flat10, show 40 + 8 * off = ([w0, w1, w2, w3, w4].flatMap unpack64).length + 8 * off by simp,
    readLE_append_right]

theorem pw_readLE_words10_lo (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) (off : Nat) (h : off < 5) :
    ByteSlice.readLE ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9].flatMap unpack64) (8 * off) 8 =
      ByteSlice.readLE ([w0, w1, w2, w3, w4].flatMap unpack64) (8 * off) 8 := by
  rw [pw_flat10, readLE_append_left _ _ _ (by simp; omega)]

theorem pw_montProj_words (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) :
    montProjOfBytes ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9].flatMap unpack64) =
      ⟨fe51ValOfBytes ([w0, w1, w2, w3, w4].flatMap unpack64) % p25519,
        fe51ValOfBytes ([w5, w6, w7, w8, w9].flatMap unpack64) % p25519⟩ := by
  have l0 := pw_readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 0 (by decide)
  have l1 := pw_readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 1 (by decide)
  have l2 := pw_readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 2 (by decide)
  have l3 := pw_readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 3 (by decide)
  have l4 := pw_readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 4 (by decide)
  have u0 := pw_readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 0 (by decide)
  have u1 := pw_readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 1 (by decide)
  have u2 := pw_readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 2 (by decide)
  have u3 := pw_readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 3 (by decide)
  have u4 := pw_readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 4 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.add_zero] at l0 l1 l2 l3 l4 u0 u1 u2 u3 u4
  simp only [montProjOfBytes, montFe51ValAt, fe51ValAt, fe51ValOfBytes, Nat.reduceAdd]
  rw [l0, l1, l2, l3, l4, u0, u1, u2, u3, u4]

theorem pw_montb_of_words (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : BitVec 64) (B : Nat)
    (hU : fe51LimbsBounded ([w0, w1, w2, w3, w4].flatMap unpack64) B)
    (hW : fe51LimbsBounded ([w5, w6, w7, w8, w9].flatMap unpack64) B) :
    montProjBounded ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9].flatMap unpack64) B := by
  have l0 := pw_readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 0 (by decide)
  have l1 := pw_readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 1 (by decide)
  have l2 := pw_readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 2 (by decide)
  have l3 := pw_readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 3 (by decide)
  have l4 := pw_readLE_words10_lo w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 4 (by decide)
  have u0 := pw_readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 0 (by decide)
  have u1 := pw_readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 1 (by decide)
  have u2 := pw_readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 2 (by decide)
  have u3 := pw_readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 3 (by decide)
  have u4 := pw_readLE_words10 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 4 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.add_zero] at l0 l1 l2 l3 l4 u0 u1 u2 u3 u4
  unfold fe51LimbsBounded at hU hW
  refine ⟨by simp, ?_, ?_⟩
  · simp only [montFe51LimbsBoundedAt, fe51LimbsBoundedAt, Nat.reduceAdd, Nat.zero_add]
    rw [l0, l1, l2, l3, l4]; exact hU.2
  · simp only [montFe51LimbsBoundedAt, fe51LimbsBoundedAt, Nat.reduceAdd]
    rw [u0, u1, u2, u3, u4]; exact hW.2

/-! ## Glue for the loop segments -/

theorem ite10 (c : Prop) [Decidable c] (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 64) :
    [if c then a0 else b0, if c then a1 else b1, if c then a2 else b2, if c then a3 else b3,
      if c then a4 else b4, if c then a5 else b5, if c then a6 else b6, if c then a7 else b7,
      if c then a8 else b8, if c then a9 else b9] =
    if c then [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] else [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] := by
  split <;> rfl

theorem cswapL (wa wb : BitVec 64) (c : Prop) [Decidable c] :
    ((wb ^^^ wa) &&& (0#64 - BitVec.setWidth 64 (if c then 0#8 else 1#8))) ^^^ wa = if c then wa else wb := by
  by_cases h : c
  · simp only [h, if_true]; exact (xor_cswap_left wa wb 0#8 (Or.inl rfl)).trans (by simp)
  · simp only [h, if_false]; exact (xor_cswap_left wa wb 1#8 (Or.inr rfl)).trans (by simp)

theorem cswapR (wa wb : BitVec 64) (c : Prop) [Decidable c] :
    ((wb ^^^ wa) &&& (0#64 - BitVec.setWidth 64 (if c then 0#8 else 1#8))) ^^^ wb = if c then wb else wa := by
  by_cases h : c
  · simp only [h, if_true]; exact (xor_cswap_right wa wb 0#8 (Or.inl rfl)).trans (by simp)
  · simp only [h, if_false]; exact (xor_cswap_right wa wb 1#8 (Or.inr rfl)).trans (by simp)

theorem sw8_32 (x : BitVec 64) : BitVec.setWidth 8 (BitVec.setWidth 32 x) = BitVec.setWidth 8 x := by
  ext i hi; simp [BitVec.getElem_setWidth]

theorem bb_mask (x : BitVec 64) (bit sv : Nat) (hb : bit < 2) (hs : sv < 2)
    (h : BitVec.setWidth 8 (BitVec.setWidth 32 x) = BitVec.setWidth 8 (BitVec.setWidth 32
      ((BitVec.setWidth 32 (BitVec.ofNat 64 bit) ^^^ BitVec.setWidth 32 (BitVec.ofNat 64 sv)).setWidth 64))) :
    BitVec.setWidth 8 x = if bit = sv then 0#8 else 1#8 := by
  rw [← sw8_32, h]
  rcases (show bit = 0 ∨ bit = 1 by omega) with rfl | rfl <;>
    rcases (show sv = 0 ∨ sv = 1 by omega) with rfl | rfl <;> decide

theorem sw_ofNat_lt (b : Nat) (hb : b < 2) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 b)).setWidth 64 = BitVec.ofNat 64 b := by
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> decide

theorem montb_ite {c : Prop} [Decidable c] {A B : List (BitVec 64)} {n : Nat}
    (hA : montProjBounded (A.flatMap unpack64) n) (hB : montProjBounded (B.flatMap unpack64) n) :
    montProjBounded ((if c then A else B).flatMap unpack64) n := by
  split <;> assumption

theorem byte_at {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ₛ bs) ∗ F) (y : BitVec 64) (i : Nat) (hy : y = BitVec.ofNat 64 i) (hi : i < bs.length) :
    m.read8 (a + y) = bs.getD i 0 ∧ m.canRead (a + y) 1 = true := by
  subst hy
  refine ⟨?_, by simpa using (sat_bytes_access hs i 1 (by omega)).1⟩
  rw [(sat_bytes_read hs i hi).1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

theorem head_cs200 (j : Nat) (hj : j < 254) :
    ConditionHolds .CS (AddWithCarry64 0#64 (~~~(BitVec.ofNat 64 (j + 1))) true).2 = false := by
  rw [cond_cs64]; simp; omega

theorem head_cs220 (j : Nat) (hj : j < 254) :
    ConditionHolds .CS (AddWithCarry64 (BitVec.ofNat 64 (j + 1)) (~~~((0x101#12).setWidth 64)) true).2 = false := by
  rw [cond_cs64]; simp; omega

theorem head_sub (j : Nat) (hj : j < 254) :
    BitVec.ofNat 64 (j + 1) - (0x001#12).setWidth 64 = BitVec.ofNat 64 j := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

theorem head_shr (j : Nat) (hj : j < 254) :
    evalBitfield .W64 .UBFM 0#64 (BitVec.ofNat 64 j) 3 63 = BitVec.ofNat 64 (j / 8) := by
  simp only [evalBitfield]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

theorem head_and7 (j : Nat) (hj : j < 254) :
    BitVec.ofNat 64 j &&& 0x0000000000000007#64 = BitVec.ofNat 64 (j % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x0000000000000007#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp; omega

theorem head_bit (w : BitVec 8) (r : Nat) (hr : r < 8) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (((w.setWidth 64).setWidth 32).setWidth 64) >>>
      ((BitVec.setWidth 32 (BitVec.ofNat 64 r)).toNat % 32))) &&& (0x0000000100000001#64).setWidth 32).setWidth 64 =
      BitVec.ofNat 64 (w.toNat / 2 ^ r % 2) := by
  have hw := w.isLt
  have e : (0x0000000100000001#64).setWidth 32 = 1#32 := by decide
  rw [e]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_and, show (1#32).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega : w.toNat < 18446744073709551616), Nat.mod_eq_of_lt (by omega : r < 32)]

theorem exit_cs200 : ConditionHolds .CS (AddWithCarry64 0#64 (~~~(BitVec.ofNat 64 0)) true).2 = true := by
  decide

theorem and255 (x : BitVec 64) : x &&& 0x00000000000000ff#64 = (x.setWidth 8).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (0x00000000000000ff#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp [BitVec.toNat_setWidth]
  omega

theorem exit_sel (x : BitVec 64) (sv : Nat) (hsv : sv < 2)
    (hx : BitVec.setWidth 8 (BitVec.setWidth 32 x) = BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.ofNat 64 sv)))
    (wa wb : BitVec 64) :
    (wb &&& (0#64 - (x &&& 0x00000000000000ff#64))) ||| (wa &&& ((x &&& 0x00000000000000ff#64) - (0x001#12).setWidth 64)) =
      if sv = 1 then wb else wa := by
  rw [and255, ← sw8_32, hx]
  rcases (show sv = 0 ∨ sv = 1 by omega) with rfl | rfl
  · have e1 : (0#64 - BitVec.setWidth 64 (BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.ofNat 64 0)))) = 0#64 := by decide
    have e2 : (BitVec.setWidth 64 (BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.ofNat 64 0))) - (0x001#12).setWidth 64) =
      BitVec.allOnes 64 := by decide
    rw [e1, e2, BitVec.and_zero, BitVec.and_allOnes, BitVec.zero_or]; rfl
  · have e1 : (0#64 - BitVec.setWidth 64 (BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.ofNat 64 1)))) =
      BitVec.allOnes 64 := by decide
    have e2 : (BitVec.setWidth 64 (BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.ofNat 64 1))) - (0x001#12).setWidth 64) =
      0#64 := by decide
    rw [e1, e2, BitVec.and_zero, BitVec.and_allOnes, BitVec.or_zero]; rfl

theorem montb_mono {bs : List (BitVec 8)} {a b : Nat} (h : montProjBounded bs a) (hab : a ≤ b) :
    montProjBounded bs b := by
  obtain ⟨hl, ⟨h1, h2, h3, h4, h5⟩, ⟨g1, g2, g3, g4, g5⟩⟩ := h
  exact ⟨hl, ⟨by omega, by omega, by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega, by omega, by omega⟩⟩

theorem ro_read64 {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ᵣ bs) ∗ F) (k : Nat) (hk : k + 8 ≤ bs.length) :
    m.read64 (a + BitVec.ofNat 64 k) = ByteSlice.readLE bs k 8 ∧
      m.canRead (a + BitVec.ofNat 64 k) 8 = true := by
  have e : ∀ i, a + BitVec.ofNat 64 k + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (k + i) := by
    intro i; rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨?_, canRead_of (fun i hi => ?_)⟩
  · have g : ∀ i, i < 8 → m.read8 (a + BitVec.ofNat 64 k + BitVec.ofNat 64 i) = bs.getD (k + i) 0 := by
      intro i hi
      rw [e, (sat_bytesRO_read hs (k + i) (by omega)).1, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      rfl
    have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega)
    have g3 := g 3 (by omega); have g4 := g 4 (by omega); have g5 := g 5 (by omega)
    have g6 := g 6 (by omega); have g7 := g 7 (by omega)
    simp only [BitVec.ofNat_eq_ofNat] at g0 g1 g2 g3 g4 g5 g6 g7
    rw [readLE8_eq]
    simp only [Memory.read64]
    rw [g0, g1, g2, g3, g4, g5, g6, g7]
    rfl
  · rw [e]; have := sat_bytesRO_read hs (k + i) (by omega); exact ⟨this.2.1, this.2.2⟩

theorem one_read {mpl : Arm64.Obj.MultiPlacement} {m : Memory} {F : SepProp}
    (hs : m ⊨ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ F) :
    (m.read64 (fe51_one mpl + BitVec.ofNat 64 (8 * 0)) = 1#64 ∧ m.canRead (fe51_one mpl + BitVec.ofNat 64 (8 * 0)) 8 = true) ∧
    (m.read64 (fe51_one mpl + BitVec.ofNat 64 (8 * 1)) = 0#64 ∧ m.canRead (fe51_one mpl + BitVec.ofNat 64 (8 * 1)) 8 = true) ∧
    (m.read64 (fe51_one mpl + BitVec.ofNat 64 (8 * 2)) = 0#64 ∧ m.canRead (fe51_one mpl + BitVec.ofNat 64 (8 * 2)) 8 = true) ∧
    (m.read64 (fe51_one mpl + BitVec.ofNat 64 (8 * 3)) = 0#64 ∧ m.canRead (fe51_one mpl + BitVec.ofNat 64 (8 * 3)) 8 = true) := by
  have l : fe51OneBytes.length = 40 := by decide +kernel
  have r0 := ro_read64 hs 0 (by rw [l]; decide)
  have r1 := ro_read64 hs 8 (by rw [l]; decide)
  have r2 := ro_read64 hs 16 (by rw [l]; decide)
  have r3 := ro_read64 hs 24 (by rw [l]; decide)
  have v0 : ByteSlice.readLE fe51OneBytes 0 8 = 1#64 := by decide +kernel
  have v1 : ByteSlice.readLE fe51OneBytes 8 8 = 0#64 := by decide +kernel
  have v2 : ByteSlice.readLE fe51OneBytes 16 8 = 0#64 := by decide +kernel
  have v3 : ByteSlice.readLE fe51OneBytes 24 8 = 0#64 := by decide +kernel
  rw [v0] at r0; rw [v1] at r1; rw [v2] at r2; rw [v3] at r3
  exact ⟨r0, r1, r2, r3⟩

theorem entry_low (x : BitVec 64) (b : Nat) (hb : b < 2)
    (hx : BitVec.setWidth 8 (BitVec.setWidth 32 x) = BitVec.ofNat 8 b) :
    ((BitVec.setWidth 32 ((BitVec.setWidth 32 x).setWidth 64)) &&& (0x000000ff000000ff#64).setWidth 32).setWidth 64 =
      BitVec.ofNat 64 b := by
  have e : ((BitVec.setWidth 32 ((BitVec.setWidth 32 x).setWidth 64)) &&& (0x000000ff000000ff#64).setWidth 32) =
      BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.setWidth 32 x)) := by
    rw [sw_32_64]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show ((0x000000ff000000ff#64).setWidth 32).toNat = 2 ^ 8 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    simp [BitVec.toNat_setWidth]
    omega
  rw [e, hx]
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> decide

theorem entry_hc564 (b : Nat) (hb : b < 2) :
    ConditionHolds .EQ (AddWithCarry32 (BitVec.setWidth 32 (BitVec.ofNat 64 b))
      (~~~BitVec.setWidth 32 (BitVec.setWidth 64 (0x002#12))) true).2 = false := by
  rw [cond_eq32]
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> decide

theorem ubfm_3_53 (x : BitVec 64) : evalBitfield .W64 .UBFM 0#64 x 3 53 = (x >>> 3) &&& 2251799813685247#64 := by
  simp [evalBitfield]
theorem ubfm_6_56 (x : BitVec 64) : evalBitfield .W64 .UBFM 0#64 x 6 56 = (x >>> 6) &&& 2251799813685247#64 := by
  simp [evalBitfield]
theorem ubfm_1_51 (x : BitVec 64) : evalBitfield .W64 .UBFM 0#64 x 1 51 = (x >>> 1) &&& 2251799813685247#64 := by
  simp [evalBitfield]
theorem ubfm_12_62 (x : BitVec 64) : evalBitfield .W64 .UBFM 0#64 x 12 62 = (x >>> 12) &&& 2251799813685247#64 := by
  simp [evalBitfield]

end X25519Dalek.LP

end
end

section
section
/-! # Block 15's calls: `black_box`, `Rev::nth`, `differential_add_and_double`, `as_affine`

Each lemma runs the `bl` and the callee from its contract, with the caller's operands held as word
lists; after the return the register file is `csMerge r sf.regs.regs`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj

abbrev bbName : String := "subtle::black_box::<u8>"
abbrev dadName : String := "curve25519_dalek::montgomery::differential_add_and_double"
abbrev aaName : String := "<curve25519_dalek::montgomery::ProjectivePoint>::as_affine"
abbrev revName' : String :=
  "<core::iter::adapters::rev::Rev<core::iter::adapters::map::Map<core::ops::range::Range<usize>, <curve25519_dalek::scalar::Scalar>::bits_le::{closure#0}>> as core::iter::traits::iterator::Iterator>::nth"

theorem lk_bb : lookupBlockSym bbName x25519CliMultiLib.blocks = some (0, 0) := by decide +kernel
theorem lk_dad : lookupBlockSym dadName x25519CliMultiLib.blocks = some (12, 0) := by decide +kernel
theorem lk_aa : lookupBlockSym aaName x25519CliMultiLib.blocks = some (11, 0) := by decide +kernel
theorem lk_rev : lookupBlockSym revName' x25519CliMultiLib.blocks = some (4, 0) := by decide +kernel

theorem sat_pre1 {m : Memory} {φ : Prop} {A F : SepProp} (hφ : φ) (hs : m ⊨ A ∗ F) :
    m ⊨ (⌜φ⌝ ∗ A) ∗ F := by
  rw [sepConj_assoc, sat_pure_sep]; exact ⟨hφ, hs⟩

theorem words3 (a x y z : BitVec 64) :
    (a ↦₆₄* [x, y, z]) = (a ↦₆₄ x) ∗ ((a + 8#64) ↦₆₄ y) ∗ ((a + 16#64) ↦₆₄ z) := by
  rw [words_cons, words_cons, words_cons, words_nil, sepConj_emp,
    show a + 8#64 + 8#64 = a + 16#64 by bv_omega]

theorem low8_eq (s : State) : BitVec.truncate 8 (s.readReg32 Reg.x0) =
    BitVec.setWidth 8 (BitVec.setWidth 32 (s.regs.regs 0#5)) := by
  simp [State.readReg32, readGpr_eq s 0#5 (by decide), Reg.x0]

/-- A call to `black_box::<u8>` (block 0). -/
theorem call_bb {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) (k : Nat) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {s0 : State} {pc pcr : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {F : SepProp}
    (hrun : s0.status = .Running) (kf : m0.KeepsFrozen m) (hal : (sp &&& 15#64) = 0#64)
    (hf : (bprog mpl k).fetchMem m pc = some (.bl (mpl.base 0 + BitVec.ofNat 64 0 - pc)))
    (hpcr : pc + 4#64 = pcr)
    (hs : m ⊨ memRegion (sp - 16#64) 16 ∗ F)
    (hcont : ∀ (sf : State), sf.status = .Running → m0.KeepsFrozen sf.mem →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      BitVec.setWidth 8 (BitVec.setWidth 32 (sf.regs.regs 0#5)) = BitVec.setWidth 8 (BitVec.setWidth 32 (r 0#5)) →
      (sf.mem ⊨ memRegion (sp - 16#64) 16 ∗ F) →
      Reach (bprog mpl k) (mkS sf pcr (csMerge r sf.regs.regs) sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl k) (mkS s0 pc r sp ps m v) Q := by
  refine y_bl hrun hf ?_
  have hpre := sat_pre1 (φ := BitVec.truncate 8 ((mkS s0 (mpl.base 0 + BitVec.ofNat 64 0) (upd r 30#5 (pc + 4#64))
      sp ps m v).readReg32 Reg.x0) = BitVec.setWidth 8 (BitVec.setWidth 32 (r 0#5)))
    (by rw [low8_eq]; rfl) hs
  refine Reach.callS hP k fnOk_black_box_v2 lk_bb (by decide)
    (BitVec.setWidth 8 (BitVec.setWidth 32 (r 0#5))) F rfl hrun hal
    (libCodeLoaded_keepsFrozen hCL kf) (by simpa only [ToBaseSpec.toSpec, stackFrame, mkS_sp] using hpre)
    ?_ ?_ ?_ ?_
  · intro sf; exact not_sat_false
  · intro c sf; exact not_sat_false
  · intro sf; exact not_sat_false
  intro sf hrunf hspf hcs hv hpost hkf
  simp only [ToBaseSpec.toSpec, stackFrame, mkS_sp, hspf] at hpost
  simp only [sepConj_assoc] at hpost
  simp only [sepConj_left_comm _ (SepProp.pure _)] at hpost
  rw [sat_pure_sep] at hpost
  obtain ⟨hx, hpost⟩ := hpost
  have e30 : upd r 30#5 (pc + 4#64) 30#5 = pcr := by rw [upd_same, hpcr]
  rw [e30, ← csMerge_eq (cs_of_upd30 hcs)]
  exact hcont sf hrunf (kf.trans hkf) hv (by rw [← low8_eq]; exact hx) hpost

/-- A call to `Rev::nth` (block 4) with `n = 1` on the iterator `[ptr, 0, 256]`. -/
theorem call_rev {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) (k : Nat) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {s0 : State} {pc pcr : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {F : SepProp} {it sc : BitVec 64} {sbs : List (BitVec 8)}
    (hrun : s0.status = .Running) (kf : m0.KeepsFrozen m) (hal : (sp &&& 15#64) = 0#64)
    (hf : (bprog mpl k).fetchMem m pc = some (.bl (mpl.base 4 + BitVec.ofNat 64 0 - pc)))
    (hpcr : pc + 4#64 = pcr) (h0 : r 0#5 = it) (h1 : r 1#5 = 1#64) (hl : sbs.length = 32)
    (hs : m ⊨ ((it ↦₆₄* [sc, 0#64, 256#64]) ∗ (sc ↦ₛ sbs) ∗ memRegion (sp - 16#64) 16) ∗ F)
    (hcont : ∀ (sf : State), sf.status = .Running → m0.KeepsFrozen sf.mem →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      BitVec.setWidth 8 (BitVec.setWidth 32 (sf.regs.regs 0#5)) =
        BitVec.ofNat 8 (leBytesToNat sbs / 2 ^ 254 % 2) →
      (sf.mem ⊨ ((it ↦₆₄* [sc, 0#64, 254#64]) ∗ (sc ↦ₛ sbs) ∗ memRegion (sp - 16#64) 16) ∗ F) →
      Reach (bprog mpl k) (mkS sf pcr (csMerge r sf.regs.regs) sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl k) (mkS s0 pc r sp ps m v) Q := by
  refine y_bl hrun hf ?_
  rw [words3] at hs
  have hpre : m ⊨ (⌜(mkS s0 (mpl.base 4 + BitVec.ofNat 64 0) (upd r 30#5 (pc + 4#64)) sp ps m v).readReg64 Reg.x0 = it ∧
      (mkS s0 (mpl.base 4 + BitVec.ofNat 64 0) (upd r 30#5 (pc + 4#64)) sp ps m v).readReg64 Reg.x1 = 1#64 ∧
      (1#64 : BitVec 64) = 1#64 ∧ sbs.length = 32⌝ ∗ (it ↦₆₄ sc) ∗ ((it + 8#64) ↦₆₄ 0#64) ∗ (sc ↦ₛ sbs) ∗
      ((it + 16#64) ↦₆₄ 256#64) ∗ memRegion (sp - 16#64) 16) ∗ F := by
    rw [sepConj_assoc, sat_pure_sep]
    exact ⟨⟨by simp [h0], by simp [h1], rfl, hl⟩, Satisfies.of_eq hs (by ac_rfl)⟩
  refine Reach.callS hP k fnOk_bits_le_rev_nth_one_v2 lk_rev (by decide)
    (it, 1#64, sc, sbs) F rfl hrun hal
    (libCodeLoaded_keepsFrozen hCL kf) (by simpa only [ToBaseSpec.toSpec, stackFrame, mkS_sp] using hpre)
    ?_ ?_ ?_ ?_
  · intro sf; exact not_sat_false
  · intro c sf; exact not_sat_false
  · intro sf; exact not_sat_false
  intro sf hrunf hspf hcs hv hpost hkf
  simp only [ToBaseSpec.toSpec, stackFrame, mkS_sp, hspf] at hpost
  simp only [sepConj_assoc] at hpost
  simp only [sepConj_left_comm _ (SepProp.pure _)] at hpost
  rw [sat_pure_sep] at hpost
  obtain ⟨hx, hpost⟩ := hpost
  have e30 : upd r 30#5 (pc + 4#64) 30#5 = pcr := by rw [upd_same, hpcr]
  rw [e30, ← csMerge_eq (cs_of_upd30 hcs)]
  refine hcont sf hrunf (kf.trans hkf) hv (by rw [← low8_eq]; exact hx) ?_
  rw [words3]
  exact Satisfies.of_eq hpost (by ac_rfl)

/-- A call to `differential_add_and_double` (block 12) with the points and `u1` as word lists. -/
theorem call_dad {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) (k : Nat) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {s0 : State} {pc pcr : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {F : SepProp} {pa qa ua : BitVec 64} {PW QW U : List (BitVec 64)}
    (hrun : s0.status = .Running) (kf : m0.KeepsFrozen m) (hal : (sp &&& 15#64) = 0#64)
    (hf : (bprog mpl k).fetchMem m pc = some (.bl (mpl.base 12 + BitVec.ofNat 64 0 - pc)))
    (hpcr : pc + 4#64 = pcr) (h0 : r 0#5 = pa) (h1 : r 1#5 = qa) (h2 : r 2#5 = ua)
    (hs : m ⊨ ((ua ↦₆₄* U) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ (pa ↦₆₄* PW) ∗ (qa ↦₆₄* QW) ∗
      memRegion (sp - 1056#64) 1056) ∗ F)
    (hPb : montProjBounded (PW.flatMap unpack64) (2 ^ 53)) (hQb : montProjBounded (QW.flatMap unpack64) (2 ^ 53))
    (hUb : fe51LimbsBounded (U.flatMap unpack64) (2 ^ 54))
    (hcont : ∀ (sf : State) (R0 R1 : List (BitVec 64)), sf.status = .Running → m0.KeepsFrozen sf.mem →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ → R0.length = 10 → R1.length = 10 →
      montProjBounded (R0.flatMap unpack64) (2 ^ 52) → montProjBounded (R1.flatMap unpack64) (2 ^ 52) →
      montProjOfBytes (R0.flatMap unpack64) = (montDiffAddAndDouble (fe51ValOfBytes (U.flatMap unpack64) % p25519)
        (montProjOfBytes (PW.flatMap unpack64)) (montProjOfBytes (QW.flatMap unpack64))).fst →
      montProjOfBytes (R1.flatMap unpack64) = (montDiffAddAndDouble (fe51ValOfBytes (U.flatMap unpack64) % p25519)
        (montProjOfBytes (PW.flatMap unpack64)) (montProjOfBytes (QW.flatMap unpack64))).snd →
      (sf.mem ⊨ ((ua ↦₆₄* U) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ (pa ↦₆₄* R0) ∗ (qa ↦₆₄* R1) ∗
        memRegion (sp - 1056#64) 1056) ∗ F) →
      Reach (bprog mpl k) (mkS sf pcr (csMerge r sf.regs.regs) sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl k) (mkS s0 pc r sp ps m v) Q := by
  refine y_bl hrun hf ?_
  simp only [words_eq_bytes] at hs
  have hpre : m ⊨ (⌜(mkS s0 (mpl.base 12 + BitVec.ofNat 64 0) (upd r 30#5 (pc + 4#64)) sp ps m v).readReg64 Reg.x0 = pa ∧
      (mkS s0 (mpl.base 12 + BitVec.ofNat 64 0) (upd r 30#5 (pc + 4#64)) sp ps m v).readReg64 Reg.x1 = qa ∧
      (mkS s0 (mpl.base 12 + BitVec.ofNat 64 0) (upd r 30#5 (pc + 4#64)) sp ps m v).readReg64 Reg.x2 = ua ∧
      montProjBounded (PW.flatMap unpack64) (2 ^ 53) ∧ montProjBounded (QW.flatMap unpack64) (2 ^ 53) ∧
      fe51LimbsBounded (U.flatMap unpack64) (2 ^ 54)⌝ ∗ (ua ↦ₛ U.flatMap unpack64) ∗
      (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ (pa ↦ₛ PW.flatMap unpack64) ∗ (qa ↦ₛ QW.flatMap unpack64) ∗
      memRegion (sp - BitVec.ofNat 64 1056) 1056) ∗ F := by
    rw [sepConj_assoc, sat_pure_sep]
    exact ⟨⟨by simp [h0], by simp [h1], by simp [h2], hPb, hQb, hUb⟩, Satisfies.of_eq hs (by ac_rfl)⟩
  refine Reach.callS hP k fnOk_differential_add_and_double_v2 lk_dad (by decide)
    (pa, qa, ua, PW.flatMap unpack64, QW.flatMap unpack64, U.flatMap unpack64) F rfl hrun hal
    (libCodeLoaded_keepsFrozen hCL kf) (by simpa only [ToBaseSpec.toSpec, stackFrame, mkS_sp] using hpre)
    ?_ ?_ ?_ ?_
  · intro sf; exact not_sat_false
  · intro c sf; exact not_sat_false
  · intro sf; exact not_sat_false
  intro sf hrunf hspf hcs hv hpost hkf
  simp only [ToBaseSpec.toSpec, stackFrame, mkS_sp, hspf] at hpost
  try simp only [sepConj_assoc] at hpost
  try simp only [sepConj_left_comm _ (sepExists _)] at hpost
  rw [sepExists_sepConj, sat_sepExists] at hpost
  obtain ⟨po, hpost⟩ := hpost
  try simp only [sepConj_assoc] at hpost
  try simp only [sepConj_left_comm _ (sepExists _)] at hpost
  rw [sepExists_sepConj, sat_sepExists] at hpost
  obtain ⟨qo, hpost⟩ := hpost
  try simp only [sepConj_assoc] at hpost
  simp only [sepConj_left_comm _ (SepProp.pure _)] at hpost
  rw [sat_pure_sep] at hpost
  obtain ⟨⟨hpb, hqb, hpv, hqv⟩, hpost⟩ := hpost
  have e30 : upd r 30#5 (pc + 4#64) 30#5 = pcr := by rw [upd_same, hpcr]
  rw [e30, ← csMerge_eq (cs_of_upd30 hcs)]
  have hpf := chunks64_flat 10 po (by rw [hpb.1])
  have hqf := chunks64_flat 10 qo (by rw [hqb.1])
  refine hcont sf (chunks64 po 10) (chunks64 qo 10) hrunf (kf.trans hkf) hv (chunks64_length po 10)
    (chunks64_length qo 10) (by rw [hpf]; exact hpb) (by rw [hqf]; exact hqb) (by rw [hpf]; exact hpv)
    (by rw [hqf]; exact hqv) ?_
  rw [← hpf, ← hqf] at hpost
  simp only [words_eq_bytes, sepConj_assoc]
  exact Satisfies.of_eq hpost (by ac_rfl)

/-- A call to `as_affine` (block 11) with the point as a word list. -/
theorem call_aa {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) (k : Nat) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {s0 : State} {pc pcr : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {F : SepProp} {out self : BitVec 64} {SW : List (BitVec 64)} {ob : List (BitVec 8)}
    (hrun : s0.status = .Running) (kf : m0.KeepsFrozen m) (hal : (sp &&& 15#64) = 0#64)
    (hf : (bprog mpl k).fetchMem m pc = some (.bl (mpl.base 11 + BitVec.ofNat 64 0 - pc)))
    (hpcr : pc + 4#64 = pcr) (h8 : r 8#5 = out) (h0 : r 0#5 = self) (hol : ob.length = 32)
    (hs : m ⊨ ((self ↦₆₄* SW) ∗ (out ↦ₛ ob) ∗ memRegion (sp - 1312#64) 1312) ∗ F)
    (hb : montProjBounded (SW.flatMap unpack64) (2 ^ 54))
    (hcont : ∀ (sf : State), sf.status = .Running → m0.KeepsFrozen sf.mem →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      (sf.mem ⊨ ((self ↦₆₄* SW) ∗ (out ↦ₛ natToLeBytes 32 (fpMul (montProjOfBytes (SW.flatMap unpack64)).U
          (fpInv (montProjOfBytes (SW.flatMap unpack64)).W))) ∗ memRegion (sp - 1312#64) 1312) ∗ F) →
      Reach (bprog mpl k) (mkS sf pcr (csMerge r sf.regs.regs) sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl k) (mkS s0 pc r sp ps m v) Q := by
  refine y_bl hrun hf ?_
  simp only [words_eq_bytes] at hs
  have hpre := sat_pre3 (φ := (mkS s0 (mpl.base 11 + BitVec.ofNat 64 0) (upd r 30#5 (pc + 4#64)) sp ps m v).readReg64 Reg.x8 = out ∧
      (mkS s0 (mpl.base 11 + BitVec.ofNat 64 0) (upd r 30#5 (pc + 4#64)) sp ps m v).readReg64 Reg.x0 = self ∧
      ob.length = 32 ∧ montProjBounded (SW.flatMap unpack64) (2 ^ 54))
    ⟨by simp [h8], by simp [h0], hol, hb⟩ (by simpa only [sepConj_assoc] using hs)
  refine Reach.callS hP k fnOk_projectivePoint_as_affine_v2 lk_aa (by decide)
    (out, self, ob, SW.flatMap unpack64) F rfl hrun hal
    (libCodeLoaded_keepsFrozen hCL kf) (by simpa only [ToBaseSpec.toSpec, stackFrame, mkS_sp] using hpre)
    ?_ ?_ ?_ ?_
  · intro sf; exact not_sat_false
  · intro c sf; exact not_sat_false
  · intro sf; exact not_sat_false
  intro sf hrunf hspf hcs hv hpost hkf
  simp only [ToBaseSpec.toSpec, stackFrame, mkS_sp, hspf] at hpost
  have e30 : upd r 30#5 (pc + 4#64) 30#5 = pcr := by rw [upd_same, hpcr]
  rw [e30, ← csMerge_eq (cs_of_upd30 hcs)]
  refine hcont sf hrunf (kf.trans hkf) hv ?_
  simp only [words_eq_bytes]
  exact Satisfies.of_eq hpost (by ac_rfl)

theorem csplit {m : Memory} {sp : BitVec 64} {F : SepProp} (n : Nat) (hn : n ≤ 1312)
    (hs : m ⊨ memRegion (sp - 1312#64) 1312 ∗ F) :
    m ⊨ memRegion (sp - BitVec.ofNat 64 n) n ∗ (memRegion (sp - 1312#64) (1312 - n) ∗ F) := by
  have h := sat_mr_split (a := sp - 1312#64) (1312 - n) n (by omega) (sp - BitVec.ofNat 64 n)
    (by apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega)
    (by rwa [show 1312 - n + n = 1312 by omega])
  exact Satisfies.of_eq h (by ac_rfl)

theorem cmerge {m : Memory} {sp : BitVec 64} {F : SepProp} (n : Nat) (hn : n ≤ 1312)
    (hs : m ⊨ memRegion (sp - BitVec.ofNat 64 n) n ∗ (memRegion (sp - 1312#64) (1312 - n) ∗ F)) :
    m ⊨ memRegion (sp - 1312#64) 1312 ∗ F := by
  have h := sat_mr_merge (a := sp - 1312#64) (b := sp - BitVec.ofNat 64 n) (1312 - n) n (by omega)
    (by apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega)
    (Satisfies.of_eq hs (by ac_rfl))
  rwa [show 1312 - n + n = 1312 by omega] at h

theorem call_bb15 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) (k : Nat) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {s0 : State} {pc pcr : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {F : SepProp}
    (hrun : s0.status = .Running) (kf : m0.KeepsFrozen m) (hal : (sp &&& 15#64) = 0#64)
    (hf : (bprog mpl k).fetchMem m pc = some (.bl (mpl.base 0 + BitVec.ofNat 64 0 - pc)))
    (hpcr : pc + 4#64 = pcr)
    (hs : m ⊨ memRegion (sp - 1312#64) 1312 ∗ F)
    (hcont : ∀ (sf : State), sf.status = .Running → m0.KeepsFrozen sf.mem →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      BitVec.setWidth 8 (BitVec.setWidth 32 (sf.regs.regs 0#5)) = BitVec.setWidth 8 (BitVec.setWidth 32 (r 0#5)) →
      (sf.mem ⊨ memRegion (sp - 1312#64) 1312 ∗ F) →
      Reach (bprog mpl k) (mkS sf pcr (csMerge r sf.regs.regs) sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl k) (mkS s0 pc r sp ps m v) Q :=
  call_bb hP k hCL hrun kf hal hf hpcr (csplit 16 (by omega) hs)
    (fun sf h1 h2 h3 h4 h5 => hcont sf h1 h2 h3 h4 (cmerge 16 (by omega) h5))

theorem call_rev15 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) (k : Nat) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {s0 : State} {pc pcr : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {F : SepProp} {it sc : BitVec 64} {sbs : List (BitVec 8)}
    (hrun : s0.status = .Running) (kf : m0.KeepsFrozen m) (hal : (sp &&& 15#64) = 0#64)
    (hf : (bprog mpl k).fetchMem m pc = some (.bl (mpl.base 4 + BitVec.ofNat 64 0 - pc)))
    (hpcr : pc + 4#64 = pcr) (h0 : r 0#5 = it) (h1 : r 1#5 = 1#64) (hl : sbs.length = 32)
    (hs : m ⊨ (it ↦₆₄* [sc, 0#64, 256#64]) ∗ (sc ↦ₛ sbs) ∗ memRegion (sp - 1312#64) 1312 ∗ F)
    (hcont : ∀ (sf : State), sf.status = .Running → m0.KeepsFrozen sf.mem →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      BitVec.setWidth 8 (BitVec.setWidth 32 (sf.regs.regs 0#5)) =
        BitVec.ofNat 8 (leBytesToNat sbs / 2 ^ 254 % 2) →
      (sf.mem ⊨ (it ↦₆₄* [sc, 0#64, 254#64]) ∗ (sc ↦ₛ sbs) ∗ memRegion (sp - 1312#64) 1312 ∗ F) →
      Reach (bprog mpl k) (mkS sf pcr (csMerge r sf.regs.regs) sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl k) (mkS s0 pc r sp ps m v) Q := by
  have hs1 : m ⊨ memRegion (sp - 1312#64) 1312 ∗ ((it ↦₆₄* [sc, 0#64, 256#64]) ∗ (sc ↦ₛ sbs) ∗ F) :=
    Satisfies.of_eq hs (by ac_rfl)
  have hs2 := csplit 16 (by omega) hs1
  refine call_rev (F := memRegion (sp - 1312#64) (1312 - 16) ∗ F) (sc := sc) hP k hCL hrun kf hal hf hpcr h0 h1 hl
    (Satisfies.of_eq hs2 (by ac_rfl)) ?_
  intro sf h1 h2 h3 h4 h5
  refine hcont sf h1 h2 h3 h4 ?_
  have h6 := cmerge (F := (it ↦₆₄* [sc, 0#64, 254#64]) ∗ (sc ↦ₛ sbs) ∗ F) 16 (by omega)
    (Satisfies.of_eq h5 (by ac_rfl))
  exact Satisfies.of_eq h6 (by ac_rfl)

theorem call_dad15 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) (k : Nat) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {s0 : State} {pc pcr : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {F : SepProp} {pa qa ua : BitVec 64} {PW QW U : List (BitVec 64)}
    (hrun : s0.status = .Running) (kf : m0.KeepsFrozen m) (hal : (sp &&& 15#64) = 0#64)
    (hf : (bprog mpl k).fetchMem m pc = some (.bl (mpl.base 12 + BitVec.ofNat 64 0 - pc)))
    (hpcr : pc + 4#64 = pcr) (h0 : r 0#5 = pa) (h1 : r 1#5 = qa) (h2 : r 2#5 = ua)
    (hs : m ⊨ (ua ↦₆₄* U) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ (pa ↦₆₄* PW) ∗ (qa ↦₆₄* QW) ∗
      memRegion (sp - 1312#64) 1312 ∗ F)
    (hPb : montProjBounded (PW.flatMap unpack64) (2 ^ 53)) (hQb : montProjBounded (QW.flatMap unpack64) (2 ^ 53))
    (hUb : fe51LimbsBounded (U.flatMap unpack64) (2 ^ 54))
    (hcont : ∀ (sf : State) (R0 R1 : List (BitVec 64)), sf.status = .Running → m0.KeepsFrozen sf.mem →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ → R0.length = 10 → R1.length = 10 →
      montProjBounded (R0.flatMap unpack64) (2 ^ 52) → montProjBounded (R1.flatMap unpack64) (2 ^ 52) →
      montProjOfBytes (R0.flatMap unpack64) = (montDiffAddAndDouble (fe51ValOfBytes (U.flatMap unpack64) % p25519)
        (montProjOfBytes (PW.flatMap unpack64)) (montProjOfBytes (QW.flatMap unpack64))).fst →
      montProjOfBytes (R1.flatMap unpack64) = (montDiffAddAndDouble (fe51ValOfBytes (U.flatMap unpack64) % p25519)
        (montProjOfBytes (PW.flatMap unpack64)) (montProjOfBytes (QW.flatMap unpack64))).snd →
      (sf.mem ⊨ (ua ↦₆₄* U) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ (pa ↦₆₄* R0) ∗ (qa ↦₆₄* R1) ∗
        memRegion (sp - 1312#64) 1312 ∗ F) →
      Reach (bprog mpl k) (mkS sf pcr (csMerge r sf.regs.regs) sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl k) (mkS s0 pc r sp ps m v) Q := by
  have hs1 : m ⊨ memRegion (sp - 1312#64) 1312 ∗ ((ua ↦₆₄* U) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗
      (pa ↦₆₄* PW) ∗ (qa ↦₆₄* QW) ∗ F) := Satisfies.of_eq hs (by ac_rfl)
  have hs2 := csplit 1056 (by omega) hs1
  refine call_dad (F := memRegion (sp - 1312#64) (1312 - 1056) ∗ F) (U := U) (PW := PW) (QW := QW) hP k hCL hrun
    kf hal hf hpcr h0 h1 h2 (Satisfies.of_eq hs2 (by ac_rfl)) hPb hQb hUb ?_
  intro sf R0 R1 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  refine hcont sf R0 R1 a1 a2 a3 a4 a5 a6 a7 a8 a9 ?_
  have h6 := cmerge (F := (ua ↦₆₄* U) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ (pa ↦₆₄* R0) ∗
    (qa ↦₆₄* R1) ∗ F) 1056 (by omega) (Satisfies.of_eq a10 (by ac_rfl))
  exact Satisfies.of_eq h6 (by ac_rfl)

theorem call_aa15 {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) (k : Nat) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {s0 : State} {pc pcr : BitVec 64}
    {r : BitVec 5 → BitVec 64} {sp : BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {Q : State → Prop} {F : SepProp} {out self : BitVec 64} {SW : List (BitVec 64)} {ob : List (BitVec 8)}
    (hrun : s0.status = .Running) (kf : m0.KeepsFrozen m) (hal : (sp &&& 15#64) = 0#64)
    (hf : (bprog mpl k).fetchMem m pc = some (.bl (mpl.base 11 + BitVec.ofNat 64 0 - pc)))
    (hpcr : pc + 4#64 = pcr) (h8 : r 8#5 = out) (h0 : r 0#5 = self) (hol : ob.length = 32)
    (hs : m ⊨ (self ↦₆₄* SW) ∗ (out ↦ₛ ob) ∗ memRegion (sp - 1312#64) 1312 ∗ F)
    (hb : montProjBounded (SW.flatMap unpack64) (2 ^ 54))
    (hcont : ∀ (sf : State), sf.status = .Running → m0.KeepsFrozen sf.mem →
      calleeSavedVRegs sf = VRegFile.calleeSaved ⟨v⟩ →
      (sf.mem ⊨ (self ↦₆₄* SW) ∗ (out ↦ₛ natToLeBytes 32 (fpMul (montProjOfBytes (SW.flatMap unpack64)).U
          (fpInv (montProjOfBytes (SW.flatMap unpack64)).W))) ∗ memRegion (sp - 1312#64) 1312 ∗ F) →
      Reach (bprog mpl k) (mkS sf pcr (csMerge r sf.regs.regs) sp sf.pstate sf.mem sf.vregs.regs) Q) :
    Reach (bprog mpl k) (mkS s0 pc r sp ps m v) Q :=
  call_aa hP k hCL hrun kf hal hf hpcr h8 h0 hol (by simpa only [sepConj_assoc] using hs) hb
    (fun sf h1 h2 h3 h4 => hcont sf h1 h2 h3 (by simpa only [sepConj_assoc] using h4))

end X25519Dalek.LP

end
end

section
section
/-! # Reordering separating conjunctions (generated): `pickN` moves the `N`-th conjunct to the front.

Same statements as the sibling batch's `Solutions/X25519DalekField/G/P22Sep.lean`. -/

set_option autoImplicit false

namespace X25519Dalek.LP

open Arm64

theorem pick2 (A1 A2 R : SepProp) : (A1 ∗ A2 ∗ R) = (A2 ∗ A1 ∗ R) := by ac_rfl
theorem pick3 (A1 A2 A3 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ R) = (A3 ∗ A1 ∗ A2 ∗ R) := by ac_rfl
theorem pick4 (A1 A2 A3 A4 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ R) = (A4 ∗ A1 ∗ A2 ∗ A3 ∗ R) := by ac_rfl
theorem pick5 (A1 A2 A3 A4 A5 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ R) = (A5 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ R) := by ac_rfl
theorem pick6 (A1 A2 A3 A4 A5 A6 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ R) = (A6 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ R) := by ac_rfl
theorem pick7 (A1 A2 A3 A4 A5 A6 A7 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ R) = (A7 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ R) := by ac_rfl
theorem pick8 (A1 A2 A3 A4 A5 A6 A7 A8 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ R) = (A8 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ R) := by ac_rfl
theorem pick9 (A1 A2 A3 A4 A5 A6 A7 A8 A9 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ R) = (A9 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ R) := by ac_rfl
theorem pick10 (A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 R : SepProp) : (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ A10 ∗ R) = (A10 ∗ A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9 ∗ R) := by ac_rfl

end X25519Dalek.LP

end
end

section
section
/-! # Block 15, offsets 0–188 and 528–572: prologue, decoding `u`, the two initial points, `Rev::nth`
(generated by `tools_ladder/mk_b15entry.py`) -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj

set_option maxHeartbeats 8000000 in
theorem b15_entry {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {S out self sc : BitVec 64} {F : SepProp} {Q : State → Prop}
    {vo : BitVec 5 → BitVec 128} {sbs selfb : List (BitVec 8)} (hsl : sbs.length = 32) (hsell : selfb.length = 32)
    (hal : (S &&& 15#64 == 0#64) = true)
    {c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 : BitVec 64}
    {sv0 sv1 sv2 sv3 sv4 sv5 sv6 sv7 sv8 sv9 sv10 sv11 it0 it1 it2 g0 uw0 uw1 uw2 uw3 uw4 : BitVec 64}
    {xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xa8 xa9 xb0 xb1 xb2 xb3 xb4 xb5 xb6 xb7 xb8 xb9 : BitVec 64}
    {sb : State} {r : BitVec 5 → BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    (hrun : sb.status = .Running) (kf : m0.KeepsFrozen m)
    (hvs : VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨vo⟩)
    (hr0 : r 0#5 = self) (hr1 : r 1#5 = sc) (hr8 : r 8#5 = out)
    (hc19 : r 19#5 = c19) (hc20 : r 20#5 = c20) (hc21 : r 21#5 = c21) (hc22 : r 22#5 = c22) (hc23 : r 23#5 = c23)
    (hc24 : r 24#5 = c24) (hc25 : r 25#5 = c25) (hc26 : r 26#5 = c26) (hc27 : r 27#5 = c27) (hc28 : r 28#5 = c28)
    (hc29 : r 29#5 = c29) (hc30 : r 30#5 = c30)
    (hs : m ⊨ ((S - 96#64) ↦₆₄* [sv0, sv1, sv2, sv3, sv4, sv5, sv6, sv7, sv8, sv9, sv10, sv11]) ∗
      ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗
      ((S - 320#64) ↦₆₄* [xa0, xa1, xa2, xa3, xa4, xa5, xa6, xa7, xa8, xa9]) ∗
      ((S - 240#64) ↦₆₄* [xb0, xb1, xb2, xb3, xb4, xb5, xb6, xb7, xb8, xb9]) ∗
      memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ (self ↦ₛ selfb) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ F)
    (hcont : ∀ (sb' : State) (r' : BitVec 5 → BitVec 64) (ps' : PState) (m' : Memory) (v' : BitVec 5 → BitVec 128)
      (u0 u1 u2 u3 u4 : BitVec 64), sb'.status = .Running → m0.KeepsFrozen m' →
      VRegFile.calleeSaved ⟨v'⟩ = VRegFile.calleeSaved ⟨vo⟩ →
      r' 19#5 = out → r' 20#5 = 0#64 → r' 21#5 = 0#64 → r' 22#5 = BitVec.ofNat 64 (leBytesToNat sbs / 2 ^ 254 % 2) →
      r' 29#5 = S - 96#64 → r' 0#5 = BitVec.ofNat 64 0 →
      (u0.toNat < 2 ^ 51 ∧ u1.toNat < 2 ^ 51 ∧ u2.toNat < 2 ^ 51 ∧ u3.toNat < 2 ^ 51 ∧ u4.toNat < 2 ^ 51 ∧
        fe51Val u0 u1 u2 u3 u4 = decodeU255 selfb) →
      (m' ⊨ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [sc, 0#64, 254#64]) ∗ ((S - 120#64) ↦₆₄* [0#64]) ∗
        ((S - 360#64) ↦₆₄* [u0, u1, u2, u3, u4]) ∗ ((S - 320#64) ↦₆₄* [1#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]) ∗
        ((S - 240#64) ↦₆₄* [u0, u1, u2, u3, u4, 1#64, 0#64, 0#64, 0#64, 0#64]) ∗
        memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ (self ↦ₛ selfb) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ F) →
      Reach (bprog mpl 15) (mkS sb' (mpl.base 15 + BitVec.ofNat 64 248) r' (S - 368#64) ps' m' v') Q) :
    Reach (bprog mpl 15) (mkS sb (mpl.base 15) r (S - 0#64) ps m v) Q := by
  refine reach_reg (i := 0#5) hr0 ?_
  refine reach_reg (i := 1#5) hr1 ?_
  refine reach_reg (i := 8#5) hr8 ?_
  refine reach_reg (i := 19#5) hc19 ?_
  refine reach_reg (i := 20#5) hc20 ?_
  refine reach_reg (i := 21#5) hc21 ?_
  refine reach_reg (i := 22#5) hc22 ?_
  refine reach_reg (i := 23#5) hc23 ?_
  refine reach_reg (i := 24#5) hc24 ?_
  refine reach_reg (i := 25#5) hc25 ?_
  refine reach_reg (i := 26#5) hc26 ?_
  refine reach_reg (i := 27#5) hc27 ?_
  refine reach_reg (i := 28#5) hc28 ?_
  refine reach_reg (i := 29#5) hc29 ?_
  refine reach_reg (i := 30#5) hc30 ?_
  refine x_subsp hrun (c15_0 hP hCL 15 kf) rfl (aSmk S 0 368 _ (by decide)) ?_
  refine x_stp_sp (t1 := 29#5) (t2 := 30#5) (v1 := c29) (v2 := c30) (i := 0) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_4 hP hCL 15 kf) (pc4 _ 4 8 rfl) (aSS S 368 272 96 (8 * 0) (by decide)) hs (by exact (by decide : 1 < 12)) rfl rfl (fun m1 hs2 kf3 => ?_)
  replace hs2 : m1 ⊨ ((S - 96#64) ↦₆₄* [c29, c30, sv2, sv3, sv4, sv5, sv6, sv7, sv8, sv9, sv10, sv11]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 320#64) ↦₆₄* [xa0, xa1, xa2, xa3, xa4, xa5, xa6, xa7, xa8, xa9]) ∗ ((S - 240#64) ↦₆₄* [xb0, xb1, xb2, xb3, xb4, xb5, xb6, xb7, xb8, xb9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ (self ↦ₛ selfb) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ F := hs2
  replace kf3 := kf.trans kf3
  clear hs kf
  refine x_stp_sp (t1 := 28#5) (t2 := 27#5) (v1 := c28) (v2 := c27) (i := 2) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_8 hP hCL 15 kf3) (pc4 _ 8 12 rfl) (aSS S 368 288 96 (8 * 2) (by decide)) hs2 (by exact (by decide : 3 < 12)) rfl rfl (fun m4 hs5 kf6 => ?_)
  replace hs5 : m4 ⊨ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, sv4, sv5, sv6, sv7, sv8, sv9, sv10, sv11]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 320#64) ↦₆₄* [xa0, xa1, xa2, xa3, xa4, xa5, xa6, xa7, xa8, xa9]) ∗ ((S - 240#64) ↦₆₄* [xb0, xb1, xb2, xb3, xb4, xb5, xb6, xb7, xb8, xb9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ (self ↦ₛ selfb) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ F := hs5
  replace kf6 := kf3.trans kf6
  clear hs2 kf3
  refine x_stp_sp (t1 := 26#5) (t2 := 25#5) (v1 := c26) (v2 := c25) (i := 4) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_12 hP hCL 15 kf6) (pc4 _ 12 16 rfl) (aSS S 368 304 96 (8 * 4) (by decide)) hs5 (by exact (by decide : 5 < 12)) rfl rfl (fun m7 hs8 kf9 => ?_)
  replace hs8 : m7 ⊨ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, sv6, sv7, sv8, sv9, sv10, sv11]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 320#64) ↦₆₄* [xa0, xa1, xa2, xa3, xa4, xa5, xa6, xa7, xa8, xa9]) ∗ ((S - 240#64) ↦₆₄* [xb0, xb1, xb2, xb3, xb4, xb5, xb6, xb7, xb8, xb9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ (self ↦ₛ selfb) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ F := hs8
  replace kf9 := kf6.trans kf9
  clear hs5 kf6
  refine x_stp_sp (t1 := 24#5) (t2 := 23#5) (v1 := c24) (v2 := c23) (i := 6) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_16 hP hCL 15 kf9) (pc4 _ 16 20 rfl) (aSS S 368 320 96 (8 * 6) (by decide)) hs8 (by exact (by decide : 7 < 12)) rfl rfl (fun m10 hs11 kf12 => ?_)
  replace hs11 : m10 ⊨ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, sv8, sv9, sv10, sv11]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 320#64) ↦₆₄* [xa0, xa1, xa2, xa3, xa4, xa5, xa6, xa7, xa8, xa9]) ∗ ((S - 240#64) ↦₆₄* [xb0, xb1, xb2, xb3, xb4, xb5, xb6, xb7, xb8, xb9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ (self ↦ₛ selfb) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ F := hs11
  replace kf12 := kf9.trans kf12
  clear hs8 kf9
  refine x_stp_sp (t1 := 22#5) (t2 := 21#5) (v1 := c22) (v2 := c21) (i := 8) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_20 hP hCL 15 kf12) (pc4 _ 20 24 rfl) (aSS S 368 336 96 (8 * 8) (by decide)) hs11 (by exact (by decide : 9 < 12)) rfl rfl (fun m13 hs14 kf15 => ?_)
  replace hs14 : m13 ⊨ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, sv10, sv11]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 320#64) ↦₆₄* [xa0, xa1, xa2, xa3, xa4, xa5, xa6, xa7, xa8, xa9]) ∗ ((S - 240#64) ↦₆₄* [xb0, xb1, xb2, xb3, xb4, xb5, xb6, xb7, xb8, xb9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ (self ↦ₛ selfb) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ F := hs14
  replace kf15 := kf12.trans kf15
  clear hs11 kf12
  refine x_stp_sp (t1 := 20#5) (t2 := 19#5) (v1 := c20) (v2 := c19) (i := 10) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_24 hP hCL 15 kf15) (pc4 _ 24 28 rfl) (aSS S 368 352 96 (8 * 10) (by decide)) hs14 (by exact (by decide : 11 < 12)) rfl rfl (fun m16 hs17 kf18 => ?_)
  replace hs17 : m16 ⊨ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 320#64) ↦₆₄* [xa0, xa1, xa2, xa3, xa4, xa5, xa6, xa7, xa8, xa9]) ∗ ((S - 240#64) ↦₆₄* [xb0, xb1, xb2, xb3, xb4, xb5, xb6, xb7, xb8, xb9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ (self ↦ₛ selfb) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ F := hs17
  replace kf18 := kf15.trans kf18
  clear hs14 kf15
  refine x_addi_sp2 (d := 29#5) (by decide) hrun (c15_28 hP hCL 15 kf18) (pc4 _ 28 32 rfl) (aSk S 368 96 _ (by decide)) ?_
  refine x_mov (d := 9#5) (b := 0#5) (y := self) (by decide) (by decide) hrun (c15_32 hP hCL 15 kf18) (pc4 _ 32 36 rfl) rfl ?_
  refine x_mov (d := 19#5) (b := 8#5) (y := out) (by decide) (by decide) hrun (c15_36 hP hCL 15 kf18) (pc4 _ 36 40 rfl) rfl ?_
  refine x_movi0 hrun (c15_40 hP hCL 15 kf18) (pc4 _ 40 44 rfl) ?_
  rw [pick9] at hs17
  refine x_ldr_any (d := 10#5) (b := 0#5) (x := self) (A := self + BitVec.ofNat 64 6) (by decide) (by decide) hrun (c15_44 hP hCL 15 kf18) (pc4 _ 44 48 rfl) rfl rfl (bytes_read64 hs17 6 (by omega)) ?_
  refine x_ldr_anyo (d := 8#5) (b := 0#5) (x := self) (A := self + BitVec.ofNat 64 0) (by decide) (by decide) hrun (c15_48 hP hCL 15 kf18) (pc4 _ 48 52 rfl) rfl rfl (bytes_read64 hs17 0 (by omega)) ?_
  refine x_ldr_any (d := 11#5) (b := 0#5) (x := self) (A := self + BitVec.ofNat 64 12) (by decide) (by decide) hrun (c15_52 hP hCL 15 kf18) (pc4 _ 52 56 rfl) rfl rfl (bytes_read64 hs17 12 (by omega)) ?_
  refine x_ldr_any (d := 12#5) (b := 0#5) (x := self) (A := self + BitVec.ofNat 64 19) (by decide) (by decide) hrun (c15_56 hP hCL 15 kf18) (pc4 _ 56 60 rfl) rfl rfl (bytes_read64 hs17 19 (by omega)) ?_
  refine x_movzr64 (d := 21#5) (by decide) hrun (c15_60 hP hCL 15 kf18) (pc4 _ 60 64 rfl) ?_
  refine x_movzr32 (d := 0#5) (by decide) hrun (c15_64 hP hCL 15 kf18) (pc4 _ 64 68 rfl) ?_
  refine x_ubfm (d := 10#5) (a := 10#5) (i := 3) (j := 53) (x := (ByteSlice.readLE selfb 6 8)) (by decide) (by decide) hrun (c15_68 hP hCL 15 kf18) (pc4 _ 68 72 rfl) rfl (fun t68 e68 => ?_)
  refine x_andi (d := 8#5) (a := 8#5) (x := (ByteSlice.readLE selfb 0 8)) (by decide) (by decide) hrun (c15_72 hP hCL 15 kf18) (pc4 _ 72 76 rfl) rfl (fun t72 e72 => ?_)
  refine x_movz32c (d := 20#5) (c := 1#64) (by decide) hrun (c15_76 hP hCL 15 kf18) (pc4 _ 76 80 rfl) (by decide) ?_
  rw [pick6] at hs17
  refine x_strq_spu (t := 0#5) (a := (S - 320#64)) (lo := 0#64) (hi := 0#64) (i := 5) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_80 hP hCL 15 kf18) (pc4 _ 80 84 rfl) (aSS S 368 88 320 (8 * 5) (by decide)) hs17 (by exact (by decide : 6 < 10)) rfl (fun m19 hs20 kf21 => ?_)
  replace hs20 : m19 ⊨ ((S - 320#64) ↦₆₄* [xa0, xa1, xa2, xa3, xa4, 0#64, 0#64, xa7, xa8, xa9]) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 240#64) ↦₆₄* [xb0, xb1, xb2, xb3, xb4, xb5, xb6, xb7, xb8, xb9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ F := hs20
  replace kf21 := kf18.trans kf21
  clear hs17 kf18
  rw [pick6] at hs20
  refine x_stp_sp (t1 := 8#5) (t2 := 10#5) (v1 := t72) (v2 := t68) (i := 0) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_84 hP hCL 15 kf21) (pc4 _ 84 88 rfl) (aSS S 368 8 360 (8 * 0) (by decide)) hs20 (by exact (by decide : 1 < 5)) rfl rfl (fun m22 hs23 kf24 => ?_)
  replace hs23 : m22 ⊨ ((S - 360#64) ↦₆₄* [t72, t68, uw2, uw3, uw4]) ∗ ((S - 320#64) ↦₆₄* [xa0, xa1, xa2, xa3, xa4, 0#64, 0#64, xa7, xa8, xa9]) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ ((S - 240#64) ↦₆₄* [xb0, xb1, xb2, xb3, xb4, xb5, xb6, xb7, xb8, xb9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ F := hs23
  replace kf24 := kf21.trans kf24
  clear hs20 kf21
  rw [pick3] at hs23
  refine x_ldr_anyo (d := 8#5) (b := 9#5) (x := self) (A := self + BitVec.ofNat 64 24) (by decide) (by decide) hrun (c15_88 hP hCL 15 kf24) (pc4 _ 88 92 rfl) rfl rfl (bytes_read64 hs23 24 (by omega)) ?_
  refine x_ubfm (d := 9#5) (a := 11#5) (i := 6) (j := 56) (x := (ByteSlice.readLE selfb 12 8)) (by decide) (by decide) hrun (c15_92 hP hCL 15 kf24) (pc4 _ 92 96 rfl) rfl (fun t92 e92 => ?_)
  refine x_ubfm (d := 11#5) (a := 12#5) (i := 1) (j := 51) (x := (ByteSlice.readLE selfb 19 8)) (by decide) (by decide) hrun (c15_96 hP hCL 15 kf24) (pc4 _ 96 100 rfl) rfl (fun t96 e96 => ?_)
  rw [pick2] at hs23
  refine x_ldrq_spu (t := 1#5) (a := (S - 360#64)) (i := 0) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_100 hP hCL 15 kf24) (pc4 _ 100 104 rfl) (aSS S 368 8 360 (8 * 0) (by decide)) (wf1 hs23 0 (by exact (by decide : 0 < 5)) : m22.read64 _ = t72 ∧ _) (wf1 hs23 1 (by exact (by decide : 1 < 5)) : m22.read64 _ = t68 ∧ _) ?_
  rw [pick3] at hs23
  refine x_strq_spu (t := 0#5) (a := (S - 320#64)) (lo := 0#64) (hi := 0#64) (i := 7) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_104 hP hCL 15 kf24) (pc4 _ 104 108 rfl) (aSS S 368 104 320 (8 * 7) (by decide)) hs23 (by exact (by decide : 8 < 10)) rfl (fun m25 hs26 kf27 => ?_)
  replace hs26 : m25 ⊨ ((S - 320#64) ↦₆₄* [xa0, xa1, xa2, xa3, xa4, 0#64, 0#64, 0#64, 0#64, xa9]) ∗ ((S - 360#64) ↦₆₄* [t72, t68, uw2, uw3, uw4]) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ ((S - 240#64) ↦₆₄* [xb0, xb1, xb2, xb3, xb4, xb5, xb6, xb7, xb8, xb9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ F := hs26
  replace kf27 := kf24.trans kf27
  clear hs23 kf24
  refine x_ubfm (d := 8#5) (a := 8#5) (i := 12) (j := 62) (x := (ByteSlice.readLE selfb 24 8)) (by decide) (by decide) hrun (c15_108 hP hCL 15 kf27) (pc4 _ 108 112 rfl) rfl (fun t108 e108 => ?_)
  refine x_strzr_sp (i := 4) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_112 hP hCL 15 kf27) (pc4 _ 112 116 rfl) (aSS S 368 80 320 (8 * 4) (by decide)) hs26 (by exact (by decide : 4 < 10)) (fun m28 hs29 kf30 => ?_)
  replace hs29 : m28 ⊨ ((S - 320#64) ↦₆₄* [xa0, xa1, xa2, xa3, 0#64, 0#64, 0#64, 0#64, 0#64, xa9]) ∗ ((S - 360#64) ↦₆₄* [t72, t68, uw2, uw3, uw4]) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ ((S - 240#64) ↦₆₄* [xb0, xb1, xb2, xb3, xb4, xb5, xb6, xb7, xb8, xb9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ F := hs29
  replace kf30 := kf27.trans kf30
  clear hs26 kf27
  rw [pick2] at hs29
  refine x_stp_sp (t1 := 9#5) (t2 := 11#5) (v1 := t92) (v2 := t96) (i := 2) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_116 hP hCL 15 kf30) (pc4 _ 116 120 rfl) (aSS S 368 24 360 (8 * 2) (by decide)) hs29 (by exact (by decide : 3 < 5)) rfl rfl (fun m31 hs32 kf33 => ?_)
  replace hs32 : m31 ⊨ ((S - 360#64) ↦₆₄* [t72, t68, t92, t96, uw4]) ∗ ((S - 320#64) ↦₆₄* [xa0, xa1, xa2, xa3, 0#64, 0#64, 0#64, 0#64, 0#64, xa9]) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ ((S - 240#64) ↦₆₄* [xb0, xb1, xb2, xb3, xb4, xb5, xb6, xb7, xb8, xb9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ F := hs32
  replace kf33 := kf30.trans kf33
  clear hs29 kf30
  refine pair15 hP hCL kf33 hrun ?_
  rw [pick7] at hs32
  refine x_strq_spo (t := 1#5) (a := (S - 240#64)) (lo := t72) (hi := t68) (i := 0) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_128 hP hCL 15 kf33) (pc4 _ 128 132 rfl) (aSS S 368 128 240 (8 * 0) (by decide)) hs32 (by exact (by decide : 1 < 10)) rfl (fun m34 hs35 kf36 => ?_)
  replace hs35 : m34 ⊨ ((S - 240#64) ↦₆₄* [t72, t68, xb2, xb3, xb4, xb5, xb6, xb7, xb8, xb9]) ∗ ((S - 360#64) ↦₆₄* [t72, t68, t92, t96, uw4]) ∗ ((S - 320#64) ↦₆₄* [xa0, xa1, xa2, xa3, 0#64, 0#64, 0#64, 0#64, 0#64, xa9]) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ F := hs35
  replace kf36 := kf33.trans kf36
  clear hs32 kf33
  rw [pick10] at hs35
  obtain ⟨o0, o1, o2, o3⟩ := one_read hs35
  refine x_ldpq_o (t1 := 2#5) (t2 := 1#5) (b := 9#5) (x := fe51_one mpl) (a := fe51_one mpl) (i := 0) (by decide) hrun (c15_132 hP hCL 15 kf36) (pc4 _ 132 136 rfl) rfl rfl o0 o1 o2 o3 ?_
  rw [pick3] at hs35
  refine x_ldrq_spu (t := 0#5) (a := (S - 360#64)) (i := 2) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_136 hP hCL 15 kf36) (pc4 _ 136 140 rfl) (aSS S 368 24 360 (8 * 2) (by decide)) (wf1 hs35 2 (by exact (by decide : 2 < 5)) : m34.read64 _ = t92 ∧ _) (wf1 hs35 3 (by exact (by decide : 3 < 5)) : m34.read64 _ = t96 ∧ _) ?_
  refine x_str_sp (t := 8#5) (v1 := t108) (i := 4) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_140 hP hCL 15 kf36) (pc4 _ 140 144 rfl) (aSS S 368 40 360 (8 * 4) (by decide)) hs35 (by exact (by decide : 4 < 5)) rfl (fun m37 hs38 kf39 => ?_)
  replace hs38 : m37 ⊨ ((S - 360#64) ↦₆₄* [t72, t68, t92, t96, t108]) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ ((S - 240#64) ↦₆₄* [t72, t68, xb2, xb3, xb4, xb5, xb6, xb7, xb8, xb9]) ∗ ((S - 320#64) ↦₆₄* [xa0, xa1, xa2, xa3, 0#64, 0#64, 0#64, 0#64, 0#64, xa9]) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ F := hs38
  replace kf39 := kf36.trans kf39
  clear hs35 kf36
  refine x_addi_sp2 (d := 9#5) (by decide) hrun (c15_144 hP hCL 15 kf39) (pc4 _ 144 148 rfl) (aSk S 368 240 _ (by decide)) ?_
  rw [pick3] at hs38
  refine x_str_sp (t := 8#5) (v1 := t108) (i := 4) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_148 hP hCL 15 kf39) (pc4 _ 148 152 rfl) (aSS S 368 160 240 (8 * 4) (by decide)) hs38 (by exact (by decide : 4 < 10)) rfl (fun m40 hs41 kf42 => ?_)
  replace hs41 : m40 ⊨ ((S - 240#64) ↦₆₄* [t72, t68, xb2, xb3, t108, xb5, xb6, xb7, xb8, xb9]) ∗ ((S - 360#64) ↦₆₄* [t72, t68, t92, t96, t108]) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ ((S - 320#64) ↦₆₄* [xa0, xa1, xa2, xa3, 0#64, 0#64, 0#64, 0#64, 0#64, xa9]) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ F := hs41
  replace kf42 := kf39.trans kf42
  clear hs38 kf39
  refine x_movz32c (d := 8#5) (c := 256#64) (by decide) hrun (c15_152 hP hCL 15 kf42) (pc4 _ 152 156 rfl) (by decide) ?_
  rw [pick4] at hs41
  refine x_stpq_sp (t1 := 2#5) (t2 := 1#5) (a := (S - 320#64)) (lo1 := 1#64) (hi1 := 0#64) (lo2 := 0#64) (hi2 := 0#64) (i := 0) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_156 hP hCL 15 kf42) (pc4 _ 156 160 rfl) (aSS S 368 48 320 (8 * 0) (by decide)) hs41 (by exact (by decide : 3 < 10)) rfl rfl (fun m43 hs44 kf45 => ?_)
  replace hs44 : m43 ⊨ ((S - 320#64) ↦₆₄* [1#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, xa9]) ∗ ((S - 240#64) ↦₆₄* [t72, t68, xb2, xb3, t108, xb5, xb6, xb7, xb8, xb9]) ∗ ((S - 360#64) ↦₆₄* [t72, t68, t92, t96, t108]) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ F := hs44
  replace kf45 := kf42.trans kf45
  clear hs41 kf42
  refine x_strzr_sp (i := 9) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_160 hP hCL 15 kf45) (pc4 _ 160 164 rfl) (aSS S 368 120 320 (8 * 9) (by decide)) hs44 (by exact (by decide : 9 < 10)) (fun m46 hs47 kf48 => ?_)
  replace hs47 : m46 ⊨ ((S - 320#64) ↦₆₄* [1#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]) ∗ ((S - 240#64) ↦₆₄* [t72, t68, xb2, xb3, t108, xb5, xb6, xb7, xb8, xb9]) ∗ ((S - 360#64) ↦₆₄* [t72, t68, t92, t96, t108]) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ F := hs47
  replace kf48 := kf45.trans kf48
  clear hs44 kf45
  rw [pick2] at hs47
  refine x_strq_o (t := 0#5) (b := 9#5) (x := (S - 240#64)) (a := (S - 240#64)) (lo := t92) (hi := t96) (i := 2) (by decide) hrun (c15_164 hP hCL 15 kf48) (pc4 _ 164 168 rfl) rfl (aSS S 240 16 240 (8 * 2) (by decide)) hs47 (by exact (by decide : 3 < 10)) rfl (fun m49 hs50 kf51 => ?_)
  replace hs50 : m49 ⊨ ((S - 240#64) ↦₆₄* [t72, t68, t92, t96, t108, xb5, xb6, xb7, xb8, xb9]) ∗ ((S - 320#64) ↦₆₄* [1#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]) ∗ ((S - 360#64) ↦₆₄* [t72, t68, t92, t96, t108]) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ F := hs50
  replace kf51 := kf48.trans kf51
  clear hs47 kf48
  refine x_strzr_sp (i := 9) (aligned_sub hal 368 (by decide) (by decide)) hrun (c15_168 hP hCL 15 kf51) (pc4 _ 168 172 rfl) (aSS S 368 200 240 (8 * 9) (by decide)) hs50 (by exact (by decide : 9 < 10)) (fun m52 hs53 kf54 => ?_)
  replace hs53 : m52 ⊨ ((S - 240#64) ↦₆₄* [t72, t68, t92, t96, t108, xb5, xb6, xb7, xb8, 0#64]) ∗ ((S - 320#64) ↦₆₄* [1#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]) ∗ ((S - 360#64) ↦₆₄* [t72, t68, t92, t96, t108]) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ F := hs53
  replace kf54 := kf51.trans kf54
  clear hs50 kf51
  refine x_strq_u (t := 2#5) (b := 9#5) (x := (S - 240#64)) (a := (S - 240#64)) (lo := 1#64) (hi := 0#64) (i := 5) (by decide) hrun (c15_172 hP hCL 15 kf54) (pc4 _ 172 176 rfl) rfl (aSS S 240 40 240 (8 * 5) (by decide)) hs53 (by exact (by decide : 6 < 10)) rfl (fun m55 hs56 kf57 => ?_)
  replace hs56 : m55 ⊨ ((S - 240#64) ↦₆₄* [t72, t68, t92, t96, t108, 1#64, 0#64, xb7, xb8, 0#64]) ∗ ((S - 320#64) ↦₆₄* [1#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]) ∗ ((S - 360#64) ↦₆₄* [t72, t68, t92, t96, t108]) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ F := hs56
  replace kf57 := kf54.trans kf57
  clear hs53 kf54
  refine x_strq_u (t := 1#5) (b := 9#5) (x := (S - 240#64)) (a := (S - 240#64)) (lo := 0#64) (hi := 0#64) (i := 7) (by decide) hrun (c15_176 hP hCL 15 kf57) (pc4 _ 176 180 rfl) rfl (aSS S 240 56 240 (8 * 7) (by decide)) hs56 (by exact (by decide : 8 < 10)) rfl (fun m58 hs59 kf60 => ?_)
  replace hs59 : m58 ⊨ ((S - 240#64) ↦₆₄* [t72, t68, t92, t96, t108, 1#64, 0#64, 0#64, 0#64, 0#64]) ∗ ((S - 320#64) ↦₆₄* [1#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]) ∗ ((S - 360#64) ↦₆₄* [t72, t68, t92, t96, t108]) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 144#64) ↦₆₄* [it0, it1, it2]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ F := hs59
  replace kf60 := kf57.trans kf60
  clear hs56 kf57
  rw [pick7] at hs59
  refine x_stpzr_r (t1 := 1#5) (b := 29#5) (x := (S - 96#64)) (v1 := sc) (i := 0) (by decide) (by decide) hrun (c15_180 hP hCL 15 kf60) (pc4 _ 180 184 rfl) rfl (aSS S 96 18446744073709551568 144 (8 * 0) (by decide)) hs59 (by exact (by decide : 1 < 3)) rfl (fun m61 hs62 kf63 => ?_)
  replace hs62 : m61 ⊨ ((S - 144#64) ↦₆₄* [sc, 0#64, it2]) ∗ ((S - 240#64) ↦₆₄* [t72, t68, t92, t96, t108, 1#64, 0#64, 0#64, 0#64, 0#64]) ∗ ((S - 320#64) ↦₆₄* [1#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]) ∗ ((S - 360#64) ↦₆₄* [t72, t68, t92, t96, t108]) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ F := hs62
  replace kf63 := kf60.trans kf63
  clear hs59 kf60
  refine x_str_r (t := 8#5) (b := 29#5) (x := (S - 96#64)) (v1 := 256#64) (i := 2) (by decide) (by decide) hrun (c15_184 hP hCL 15 kf63) (pc4 _ 184 188 rfl) rfl (aSS S 96 18446744073709551584 144 (8 * 2) (by decide)) hs62 (by exact (by decide : 2 < 3)) rfl (fun m64 hs65 kf66 => ?_)
  replace hs65 : m64 ⊨ ((S - 144#64) ↦₆₄* [sc, 0#64, 256#64]) ∗ ((S - 240#64) ↦₆₄* [t72, t68, t92, t96, t108, 1#64, 0#64, 0#64, 0#64, 0#64]) ∗ ((S - 320#64) ↦₆₄* [1#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]) ∗ ((S - 360#64) ↦₆₄* [t72, t68, t92, t96, t108]) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 120#64) ↦₆₄* [g0]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ F := hs65
  replace kf66 := kf63.trans kf66
  clear hs62 kf63
  refine x_cbnz_t (t := 20#5) (x := 1#64) (by decide) hrun (c15_188 hP hCL 15 kf66) rfl (by decide) (pcb _ 188 340 528 (by decide)) ?_
  refine x_movw (d := 22#5) (b := 0#5) (y := 0#64) (by decide) (by decide) hrun (c15_528 hP hCL 15 kf66) (pc4 _ 528 532 rfl) rfl (fun t528 e528 => ?_)
  refine x_subi_r2 (d := 0#5) (a := 29#5) (by decide) (by decide) hrun (c15_532 hP hCL 15 kf66) (pc4 _ 532 536 rfl) rfl (aSmk S 96 144 _ (by decide)) ?_
  refine x_mov (d := 1#5) (b := 20#5) (y := 1#64) (by decide) (by decide) hrun (c15_536 hP hCL 15 kf66) (pc4 _ 536 540 rfl) rfl ?_
  rw [pick8] at hs65
  refine x_str_r (t := 21#5) (b := 29#5) (x := (S - 96#64)) (v1 := 0#64) (i := 0) (by decide) (by decide) hrun (c15_540 hP hCL 15 kf66) (pc4 _ 540 544 rfl) rfl (aSS S 96 18446744073709551592 120 (8 * 0) (by decide)) hs65 (by exact (by decide : 0 < 1)) rfl (fun m67 hs68 kf69 => ?_)
  replace hs68 : m67 ⊨ ((S - 120#64) ↦₆₄* [0#64]) ∗ ((S - 144#64) ↦₆₄* [sc, 0#64, 256#64]) ∗ ((S - 240#64) ↦₆₄* [t72, t68, t92, t96, t108, 1#64, 0#64, 0#64, 0#64, 0#64]) ∗ ((S - 320#64) ↦₆₄* [1#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]) ∗ ((S - 360#64) ↦₆₄* [t72, t68, t92, t96, t108]) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (self ↦ₛ selfb) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ (sc ↦ₛ sbs) ∗ F := hs68
  replace kf69 := kf66.trans kf69
  clear hs65 kf66
  rw [pick9] at hs68
  rw [pick10] at hs68
  rw [pick4] at hs68
  refine call_rev15 (it := (S - 144#64)) (sc := sc) hP 15 hCL hrun kf69 (aligned_sub hal 368 (by decide) (by decide)) (c15_544 hP hCL 15 kf69 lk_rev) (pc4 _ 544 548 rfl) rfl rfl hsl hs68 (fun sf544 hrun544 kf544 hv544 hx544 hs544 => ?_)
  have hvs544 : VRegFile.calleeSaved ⟨sf544.vregs.regs⟩ = VRegFile.calleeSaved ⟨vo⟩ := hv544.trans (cs_upd (by decide) (cs_upd (by decide) (cs_upd (by decide) (cs_upd (by decide) (cs_upd (by decide) hvs)))))
  refine x_movw (d := 8#5) (b := 0#5) (y := sf544.regs.regs 0#5) (by decide) (by decide) hrun544 (c15_548 hP hCL 15 kf544) (pc4 _ 548 552 rfl) rfl (fun t548 e548 => ?_)
  refine x_movw (d := 0#5) (b := 22#5) (y := t528) (by decide) (by decide) hrun544 (c15_552 hP hCL 15 kf544) (pc4 _ 552 556 rfl) rfl (fun t552 e552 => ?_)
  refine x_andiw (d := 22#5) (a := 8#5) (x := t548) (by decide) (by decide) hrun544 (c15_556 hP hCL 15 kf544) (pc4 _ 556 560 rfl) rfl (fun t556 e556 => ?_)
  refine x_cmpiw (a := 22#5) (x := t556) (by decide) hrun544 (c15_560 hP hCL 15 kf544) (pc4 _ 560 564 rfl) rfl ?_
  have h556 : t556 = BitVec.ofNat 64 (leBytesToNat sbs / 2 ^ 254 % 2) := by
    rw [e556, e548]; exact entry_low _ _ (Nat.mod_lt _ (by decide)) hx544
  have hc564 : ConditionHolds .EQ (AddWithCarry32 (BitVec.setWidth 32 t556)
      (~~~BitVec.setWidth 32 (BitVec.setWidth 64 (0x002#12))) true).2 = false := by
    rw [h556]; exact entry_hc564 _ (Nat.mod_lt _ (by decide))
  refine x_bcond_n hrun544 (c15_564 hP hCL 15 kf544) hc564 (pc4 _ 564 568 rfl) ?_
  rw [pick4] at hs544
  refine x_ldr_u (d := 20#5) (b := 29#5) (x := (S - 96#64)) (a := (S - 120#64)) (i := 0) (by decide) (by decide) hrun544 (c15_568 hP hCL 15 kf544) (pc4 _ 568 572 rfl) rfl (aSS S 96 18446744073709551592 120 (8 * 0) (by decide)) (wf1 hs544 0 (by exact (by decide : 0 < 1)) : sf544.mem.read64 _ = 0#64 ∧ _) ?_
  refine x_b hrun544 (c15_572 hP hCL 15 kf544) (pcb _ 572 18446744073709551292 248 (by decide)) ?_
  have hu := decode_limbs selfb hsell
  rw [← ubfm_3_53, ← ubfm_6_56, ← ubfm_1_51, ← ubfm_12_62, ← e72, ← e68, ← e92, ← e96, ← e108] at hu
  exact hcont _ _ _ _ _ t72 t68 t92 t96 t108 hrun544 kf544 hvs544 rfl rfl rfl (show t556 = _ from h556) rfl
    (by show t552 = _; rw [e552, e528]; decide) hu (Satisfies.of_eq hs544 (by ac_rfl))

end X25519Dalek.LP

end
end

section
section
/-! # Block 15, offsets 248–524: one ladder step (`black_box`, the constant-time swap, `differential_add_and_double`)

Generated by `tools_ladder/mk_b15mid.py` from `gen_b15.py mid`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj

set_option maxHeartbeats 8000000 in
theorem b15_mid {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {S out : BitVec 64} {F : SepProp} {Q : State → Prop}
    {vo : BitVec 5 → BitVec 128} (hal : (S &&& 15#64 == 0#64) = true)
    {sb : State} {r : BitVec 5 → BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {uw0 uw1 uw2 uw3 uw4 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 64}
    {bb : BitVec 8} {bit sv : Nat}
    (hrun : sb.status = .Running) (kf : m0.KeepsFrozen m)
    (hvs : VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨vo⟩)
    (hr19 : r 19#5 = out) (hr20 : r 20#5 = 0#64) (hr21 : r 21#5 = 0#64) (hr22 : r 22#5 = BitVec.ofNat 64 bit)
    (hr29 : r 29#5 = S - 96#64) (hr0 : r 0#5 = BitVec.ofNat 64 sv) (hbit : bit < 2) (hsv : sv < 2)
    (hA : montProjBounded ([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].flatMap unpack64) (2 ^ 53))
    (hB : montProjBounded ([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9].flatMap unpack64) (2 ^ 53))
    (hUb : fe51LimbsBounded ([uw0, uw1, uw2, uw3, uw4].flatMap unpack64) (2 ^ 54))
    (hs : m ⊨ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 320#64) ↦₆₄* [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]) ∗
      ((S - 240#64) ↦₆₄* [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗
      (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ F)
    (hcont : ∀ (sb' : State) (r' : BitVec 5 → BitVec 64) (ps' : PState) (m' : Memory) (v' : BitVec 5 → BitVec 128)
      (R0 R1 : List (BitVec 64)), sb'.status = .Running → m0.KeepsFrozen m' →
      VRegFile.calleeSaved ⟨v'⟩ = VRegFile.calleeSaved ⟨vo⟩ →
      r' 19#5 = out → r' 21#5 = 0#64 → r' 29#5 = S - 96#64 → r' 0#5 = BitVec.ofNat 64 bit →
      R0.length = 10 → R1.length = 10 →
      montProjBounded (R0.flatMap unpack64) (2 ^ 52) → montProjBounded (R1.flatMap unpack64) (2 ^ 52) →
      montProjOfBytes (R0.flatMap unpack64) = (montDiffAddAndDouble (fe51ValOfBytes ([uw0, uw1, uw2, uw3, uw4].flatMap unpack64) % p25519)
        (montProjOfBytes ((if bit = sv then [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] else [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]).flatMap unpack64))
        (montProjOfBytes ((if bit = sv then [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] else [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]).flatMap unpack64))).fst →
      montProjOfBytes (R1.flatMap unpack64) = (montDiffAddAndDouble (fe51ValOfBytes ([uw0, uw1, uw2, uw3, uw4].flatMap unpack64) % p25519)
        (montProjOfBytes ((if bit = sv then [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] else [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]).flatMap unpack64))
        (montProjOfBytes ((if bit = sv then [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] else [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]).flatMap unpack64))).snd →
      (m' ⊨ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 320#64) ↦₆₄* R0) ∗ ((S - 240#64) ↦₆₄* R1) ∗
        ((S - 148#64) ↦ₛ [(BitVec.ofNat 64 bit).setWidth 8]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗
        (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ F) →
      Reach (bprog mpl 15) (mkS sb' (mpl.base 15 + BitVec.ofNat 64 192) r' (S - 368#64) ps' m' v') Q) :
    Reach (bprog mpl 15) (mkS sb (mpl.base 15 + BitVec.ofNat 64 248) r (S - 368#64) ps m v) Q := by
  refine reach_reg (i := 19#5) hr19 ?_
  refine reach_reg (i := 20#5) hr20 ?_
  refine reach_reg (i := 21#5) hr21 ?_
  refine reach_reg (i := 22#5) hr22 ?_
  refine reach_reg (i := 29#5) hr29 ?_
  refine reach_reg (i := 0#5) hr0 ?_
  refine x_eorw (d := 0#5) (a := 22#5) (b := 0#5) (x := BitVec.ofNat 64 bit) (y := BitVec.ofNat 64 sv) (by decide) (by decide) (by decide) hrun (c15_248 hP hCL 15 kf) (pc4 _ 248 252 rfl) rfl rfl (fun t248 e248 => ?_)
  rw [pick5] at hs
  refine call_bb15 hP 15 hCL hrun kf (aligned_sub hal 368 (by decide) (by decide)) (c15_252 hP hCL 15 kf lk_bb) (pc4 _ 252 256 rfl) hs (fun sf252 hrun252 kf252 hv252 hx252 hs252 => ?_)
  have hvs252 : VRegFile.calleeSaved ⟨sf252.vregs.regs⟩ = VRegFile.calleeSaved ⟨vo⟩ := hv252.trans hvs
  rw [pick3] at hs252
  refine x_ldp_sp (d1 := 16#5) (d2 := 18#5) (a := (S - 320#64)) (i := 0) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_256 hP hCL 15 kf252) (pc4 _ 256 260 rfl) (aSS S 368 48 320 (8 * 0) (by decide)) (wf1 hs252 0 (by exact (by decide : 0 < 10)) : sf252.mem.read64 _ = a0 ∧ _) rfl (wf1 hs252 1 (by exact (by decide : 1 < 10)) : sf252.mem.read64 _ = a1 ∧ _) ?_
  refine x_subuxtb (d := 10#5) (a := 21#5) (b := 0#5) (x := 0#64) (y := sf252.regs.regs 0#5) (by decide) (by decide) (by decide) hrun252 (c15_260 hP hCL 15 kf252) (pc4 _ 260 264 rfl) rfl rfl (fun t260 e260 => ?_)
  rw [pick4] at hs252
  refine x_ldp_sp (d1 := 8#5) (d2 := 11#5) (a := (S - 240#64)) (i := 0) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_264 hP hCL 15 kf252) (pc4 _ 264 268 rfl) (aSS S 368 128 240 (8 * 0) (by decide)) (wf1 hs252 0 (by exact (by decide : 0 < 10)) : sf252.mem.read64 _ = b0 ∧ _) rfl (wf1 hs252 1 (by exact (by decide : 1 < 10)) : sf252.mem.read64 _ = b1 ∧ _) ?_
  rw [pick2] at hs252
  refine x_ldp_sp (d1 := 0#5) (d2 := 5#5) (a := (S - 320#64)) (i := 2) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_268 hP hCL 15 kf252) (pc4 _ 268 272 rfl) (aSS S 368 64 320 (8 * 2) (by decide)) (wf1 hs252 2 (by exact (by decide : 2 < 10)) : sf252.mem.read64 _ = a2 ∧ _) rfl (wf1 hs252 3 (by exact (by decide : 3 < 10)) : sf252.mem.read64 _ = a3 ∧ _) ?_
  refine x_ldp_sp (d1 := 6#5) (d2 := 7#5) (a := (S - 320#64)) (i := 4) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_272 hP hCL 15 kf252) (pc4 _ 272 276 rfl) (aSS S 368 80 320 (8 * 4) (by decide)) (wf1 hs252 4 (by exact (by decide : 4 < 10)) : sf252.mem.read64 _ = a4 ∧ _) rfl (wf1 hs252 5 (by exact (by decide : 5 < 10)) : sf252.mem.read64 _ = a5 ∧ _) ?_
  refine x_eor (d := 9#5) (a := 8#5) (b := 16#5) (x := b0) (y := a0) (by decide) (by decide) (by decide) hrun252 (c15_276 hP hCL 15 kf252) (pc4 _ 276 280 rfl) rfl rfl (fun t276 e276 => ?_)
  subst e276
  refine x_eor (d := 14#5) (a := 11#5) (b := 18#5) (x := b1) (y := a1) (by decide) (by decide) (by decide) hrun252 (c15_280 hP hCL 15 kf252) (pc4 _ 280 284 rfl) rfl rfl (fun t280 e280 => ?_)
  subst e280
  refine x_and (d := 13#5) (a := 9#5) (b := 10#5) (x := (b0 ^^^ a0)) (y := t260) (by decide) (by decide) (by decide) hrun252 (c15_284 hP hCL 15 kf252) (pc4 _ 284 288 rfl) rfl rfl (fun t284 e284 => ?_)
  subst e284
  rw [pick2] at hs252
  refine x_ldp_sp (d1 := 9#5) (d2 := 12#5) (a := (S - 240#64)) (i := 2) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_288 hP hCL 15 kf252) (pc4 _ 288 292 rfl) (aSS S 368 144 240 (8 * 2) (by decide)) (wf1 hs252 2 (by exact (by decide : 2 < 10)) : sf252.mem.read64 _ = b2 ∧ _) rfl (wf1 hs252 3 (by exact (by decide : 3 < 10)) : sf252.mem.read64 _ = b3 ∧ _) ?_
  refine x_and (d := 17#5) (a := 14#5) (b := 10#5) (x := (b1 ^^^ a1)) (y := t260) (by decide) (by decide) (by decide) hrun252 (c15_292 hP hCL 15 kf252) (pc4 _ 292 296 rfl) rfl rfl (fun t292 e292 => ?_)
  subst e292
  refine x_eor (d := 24#5) (a := 13#5) (b := 16#5) (x := ((b0 ^^^ a0) &&& t260)) (y := a0) (by decide) (by decide) (by decide) hrun252 (c15_296 hP hCL 15 kf252) (pc4 _ 296 300 rfl) rfl rfl (fun t296 e296 => ?_)
  subst e296
  refine x_eor (d := 8#5) (a := 13#5) (b := 8#5) (x := ((b0 ^^^ a0) &&& t260)) (y := b0) (by decide) (by decide) (by decide) hrun252 (c15_300 hP hCL 15 kf252) (pc4 _ 300 304 rfl) rfl rfl (fun t300 e300 => ?_)
  subst e300
  refine x_eor (d := 25#5) (a := 17#5) (b := 18#5) (x := ((b1 ^^^ a1) &&& t260)) (y := a1) (by decide) (by decide) (by decide) hrun252 (c15_304 hP hCL 15 kf252) (pc4 _ 304 308 rfl) rfl rfl (fun t304 e304 => ?_)
  subst e304
  rw [pick2] at hs252
  refine x_ldp_sp (d1 := 23#5) (d2 := 3#5) (a := (S - 320#64)) (i := 6) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_308 hP hCL 15 kf252) (pc4 _ 308 312 rfl) (aSS S 368 96 320 (8 * 6) (by decide)) (wf1 hs252 6 (by exact (by decide : 6 < 10)) : sf252.mem.read64 _ = a6 ∧ _) rfl (wf1 hs252 7 (by exact (by decide : 7 < 10)) : sf252.mem.read64 _ = a7 ∧ _) ?_
  refine x_eor (d := 15#5) (a := 9#5) (b := 0#5) (x := b2) (y := a2) (by decide) (by decide) (by decide) hrun252 (c15_312 hP hCL 15 kf252) (pc4 _ 312 316 rfl) rfl rfl (fun t312 e312 => ?_)
  subst e312
  refine x_eor (d := 18#5) (a := 12#5) (b := 5#5) (x := b3) (y := a3) (by decide) (by decide) (by decide) hrun252 (c15_316 hP hCL 15 kf252) (pc4 _ 316 320 rfl) rfl rfl (fun t316 e316 => ?_)
  subst e316
  refine x_stp_sp (t1 := 24#5) (t2 := 25#5) (v1 := (((b0 ^^^ a0) &&& t260) ^^^ a0)) (v2 := (((b1 ^^^ a1) &&& t260) ^^^ a1)) (i := 0) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_320 hP hCL 15 kf252) (pc4 _ 320 324 rfl) (aSS S 368 48 320 (8 * 0) (by decide)) hs252 (by exact (by decide : 1 < 10)) rfl rfl (fun m1 hs2 kf3 => ?_)
  replace hs2 : m1 ⊨ ((S - 320#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ a0), (((b1 ^^^ a1) &&& t260) ^^^ a1), a2, a3, a4, a5, a6, a7, a8, a9]) ∗ ((S - 240#64) ↦₆₄* [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ F := hs2
  replace kf3 := kf252.trans kf3
  clear hs252 kf252
  refine x_and (d := 14#5) (a := 15#5) (b := 10#5) (x := (b2 ^^^ a2)) (y := t260) (by decide) (by decide) (by decide) hrun252 (c15_324 hP hCL 15 kf3) (pc4 _ 324 328 rfl) rfl rfl (fun t324 e324 => ?_)
  subst e324
  rw [pick2] at hs2
  refine x_ldp_sp (d1 := 15#5) (d2 := 16#5) (a := (S - 240#64)) (i := 4) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_328 hP hCL 15 kf3) (pc4 _ 328 332 rfl) (aSS S 368 160 240 (8 * 4) (by decide)) (wf1 hs2 4 (by exact (by decide : 4 < 10)) : m1.read64 _ = b4 ∧ _) rfl (wf1 hs2 5 (by exact (by decide : 5 < 10)) : m1.read64 _ = b5 ∧ _) ?_
  refine x_eor (d := 26#5) (a := 14#5) (b := 0#5) (x := ((b2 ^^^ a2) &&& t260)) (y := a2) (by decide) (by decide) (by decide) hrun252 (c15_332 hP hCL 15 kf3) (pc4 _ 332 336 rfl) rfl rfl (fun t332 e332 => ?_)
  subst e332
  refine x_and (d := 2#5) (a := 18#5) (b := 10#5) (x := (b3 ^^^ a3)) (y := t260) (by decide) (by decide) (by decide) hrun252 (c15_336 hP hCL 15 kf3) (pc4 _ 336 340 rfl) rfl rfl (fun t336 e336 => ?_)
  subst e336
  refine x_eor (d := 11#5) (a := 17#5) (b := 11#5) (x := ((b1 ^^^ a1) &&& t260)) (y := b1) (by decide) (by decide) (by decide) hrun252 (c15_340 hP hCL 15 kf3) (pc4 _ 340 344 rfl) rfl rfl (fun t340 e340 => ?_)
  subst e340
  refine x_eor (d := 5#5) (a := 2#5) (b := 5#5) (x := ((b3 ^^^ a3) &&& t260)) (y := a3) (by decide) (by decide) (by decide) hrun252 (c15_344 hP hCL 15 kf3) (pc4 _ 344 348 rfl) rfl rfl (fun t344 e344 => ?_)
  subst e344
  rw [pick2] at hs2
  refine x_ldp_sp (d1 := 4#5) (d2 := 1#5) (a := (S - 320#64)) (i := 8) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_348 hP hCL 15 kf3) (pc4 _ 348 352 rfl) (aSS S 368 112 320 (8 * 8) (by decide)) (wf1 hs2 8 (by exact (by decide : 8 < 10)) : m1.read64 _ = a8 ∧ _) rfl (wf1 hs2 9 (by exact (by decide : 9 < 10)) : m1.read64 _ = a9 ∧ _) ?_
  refine x_eor (d := 0#5) (a := 15#5) (b := 6#5) (x := b4) (y := a4) (by decide) (by decide) (by decide) hrun252 (c15_352 hP hCL 15 kf3) (pc4 _ 352 356 rfl) rfl rfl (fun t352 e352 => ?_)
  subst e352
  refine x_eor (d := 27#5) (a := 16#5) (b := 7#5) (x := b5) (y := a5) (by decide) (by decide) (by decide) hrun252 (c15_356 hP hCL 15 kf3) (pc4 _ 356 360 rfl) rfl rfl (fun t356 e356 => ?_)
  subst e356
  refine x_stp_sp (t1 := 26#5) (t2 := 5#5) (v1 := (((b2 ^^^ a2) &&& t260) ^^^ a2)) (v2 := (((b3 ^^^ a3) &&& t260) ^^^ a3)) (i := 2) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_360 hP hCL 15 kf3) (pc4 _ 360 364 rfl) (aSS S 368 64 320 (8 * 2) (by decide)) hs2 (by exact (by decide : 3 < 10)) rfl rfl (fun m4 hs5 kf6 => ?_)
  replace hs5 : m4 ⊨ ((S - 320#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ a0), (((b1 ^^^ a1) &&& t260) ^^^ a1), (((b2 ^^^ a2) &&& t260) ^^^ a2), (((b3 ^^^ a3) &&& t260) ^^^ a3), a4, a5, a6, a7, a8, a9]) ∗ ((S - 240#64) ↦₆₄* [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ F := hs5
  replace kf6 := kf3.trans kf6
  clear hs2 kf3
  refine x_and (d := 18#5) (a := 0#5) (b := 10#5) (x := (b4 ^^^ a4)) (y := t260) (by decide) (by decide) (by decide) hrun252 (c15_364 hP hCL 15 kf6) (pc4 _ 364 368 rfl) rfl rfl (fun t364 e364 => ?_)
  subst e364
  rw [pick2] at hs5
  refine x_ldp_sp (d1 := 0#5) (d2 := 28#5) (a := (S - 240#64)) (i := 6) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_368 hP hCL 15 kf6) (pc4 _ 368 372 rfl) (aSS S 368 176 240 (8 * 6) (by decide)) (wf1 hs5 6 (by exact (by decide : 6 < 10)) : m4.read64 _ = b6 ∧ _) rfl (wf1 hs5 7 (by exact (by decide : 7 < 10)) : m4.read64 _ = b7 ∧ _) ?_
  refine x_and (d := 24#5) (a := 27#5) (b := 10#5) (x := (b5 ^^^ a5)) (y := t260) (by decide) (by decide) (by decide) hrun252 (c15_372 hP hCL 15 kf6) (pc4 _ 372 376 rfl) rfl rfl (fun t372 e372 => ?_)
  subst e372
  refine x_eor (d := 6#5) (a := 18#5) (b := 6#5) (x := ((b4 ^^^ a4) &&& t260)) (y := a4) (by decide) (by decide) (by decide) hrun252 (c15_376 hP hCL 15 kf6) (pc4 _ 376 380 rfl) rfl rfl (fun t376 e376 => ?_)
  subst e376
  refine x_stp_sp (t1 := 8#5) (t2 := 11#5) (v1 := (((b0 ^^^ a0) &&& t260) ^^^ b0)) (v2 := (((b1 ^^^ a1) &&& t260) ^^^ b1)) (i := 0) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_380 hP hCL 15 kf6) (pc4 _ 380 384 rfl) (aSS S 368 128 240 (8 * 0) (by decide)) hs5 (by exact (by decide : 1 < 10)) rfl rfl (fun m7 hs8 kf9 => ?_)
  replace hs8 : m7 ⊨ ((S - 240#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ b0), (((b1 ^^^ a1) &&& t260) ^^^ b1), b2, b3, b4, b5, b6, b7, b8, b9]) ∗ ((S - 320#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ a0), (((b1 ^^^ a1) &&& t260) ^^^ a1), (((b2 ^^^ a2) &&& t260) ^^^ a2), (((b3 ^^^ a3) &&& t260) ^^^ a3), a4, a5, a6, a7, a8, a9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ F := hs8
  replace kf9 := kf6.trans kf9
  clear hs5 kf6
  refine x_eor (d := 7#5) (a := 24#5) (b := 7#5) (x := ((b5 ^^^ a5) &&& t260)) (y := a5) (by decide) (by decide) (by decide) hrun252 (c15_384 hP hCL 15 kf9) (pc4 _ 384 388 rfl) rfl rfl (fun t384 e384 => ?_)
  subst e384
  refine x_eor (d := 8#5) (a := 14#5) (b := 9#5) (x := ((b2 ^^^ a2) &&& t260)) (y := b2) (by decide) (by decide) (by decide) hrun252 (c15_388 hP hCL 15 kf9) (pc4 _ 388 392 rfl) rfl rfl (fun t388 e388 => ?_)
  subst e388
  refine x_eor (d := 9#5) (a := 2#5) (b := 12#5) (x := ((b3 ^^^ a3) &&& t260)) (y := b3) (by decide) (by decide) (by decide) hrun252 (c15_392 hP hCL 15 kf9) (pc4 _ 392 396 rfl) rfl rfl (fun t392 e392 => ?_)
  subst e392
  refine x_eor (d := 25#5) (a := 28#5) (b := 3#5) (x := b7) (y := a7) (by decide) (by decide) (by decide) hrun252 (c15_396 hP hCL 15 kf9) (pc4 _ 396 400 rfl) rfl rfl (fun t396 e396 => ?_)
  subst e396
  refine x_eor (d := 30#5) (a := 0#5) (b := 23#5) (x := b6) (y := a6) (by decide) (by decide) (by decide) hrun252 (c15_400 hP hCL 15 kf9) (pc4 _ 400 404 rfl) rfl rfl (fun t400 e400 => ?_)
  subst e400
  rw [pick2] at hs8
  refine x_stp_sp (t1 := 6#5) (t2 := 7#5) (v1 := (((b4 ^^^ a4) &&& t260) ^^^ a4)) (v2 := (((b5 ^^^ a5) &&& t260) ^^^ a5)) (i := 4) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_404 hP hCL 15 kf9) (pc4 _ 404 408 rfl) (aSS S 368 80 320 (8 * 4) (by decide)) hs8 (by exact (by decide : 5 < 10)) rfl rfl (fun m10 hs11 kf12 => ?_)
  replace hs11 : m10 ⊨ ((S - 320#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ a0), (((b1 ^^^ a1) &&& t260) ^^^ a1), (((b2 ^^^ a2) &&& t260) ^^^ a2), (((b3 ^^^ a3) &&& t260) ^^^ a3), (((b4 ^^^ a4) &&& t260) ^^^ a4), (((b5 ^^^ a5) &&& t260) ^^^ a5), a6, a7, a8, a9]) ∗ ((S - 240#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ b0), (((b1 ^^^ a1) &&& t260) ^^^ b1), b2, b3, b4, b5, b6, b7, b8, b9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ F := hs11
  replace kf12 := kf9.trans kf12
  clear hs8 kf9
  refine x_and (d := 5#5) (a := 25#5) (b := 10#5) (x := (b7 ^^^ a7)) (y := t260) (by decide) (by decide) (by decide) hrun252 (c15_408 hP hCL 15 kf12) (pc4 _ 408 412 rfl) rfl rfl (fun t408 e408 => ?_)
  subst e408
  rw [pick2] at hs11
  refine x_ldp_sp (d1 := 26#5) (d2 := 25#5) (a := (S - 240#64)) (i := 8) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_412 hP hCL 15 kf12) (pc4 _ 412 416 rfl) (aSS S 368 192 240 (8 * 8) (by decide)) (wf1 hs11 8 (by exact (by decide : 8 < 10)) : m10.read64 _ = b8 ∧ _) rfl (wf1 hs11 9 (by exact (by decide : 9 < 10)) : m10.read64 _ = b9 ∧ _) ?_
  refine x_and (d := 27#5) (a := 30#5) (b := 10#5) (x := (b6 ^^^ a6)) (y := t260) (by decide) (by decide) (by decide) hrun252 (c15_416 hP hCL 15 kf12) (pc4 _ 416 420 rfl) rfl rfl (fun t416 e416 => ?_)
  subst e416
  refine x_stp_sp (t1 := 8#5) (t2 := 9#5) (v1 := (((b2 ^^^ a2) &&& t260) ^^^ b2)) (v2 := (((b3 ^^^ a3) &&& t260) ^^^ b3)) (i := 2) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_420 hP hCL 15 kf12) (pc4 _ 420 424 rfl) (aSS S 368 144 240 (8 * 2) (by decide)) hs11 (by exact (by decide : 3 < 10)) rfl rfl (fun m13 hs14 kf15 => ?_)
  replace hs14 : m13 ⊨ ((S - 240#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ b0), (((b1 ^^^ a1) &&& t260) ^^^ b1), (((b2 ^^^ a2) &&& t260) ^^^ b2), (((b3 ^^^ a3) &&& t260) ^^^ b3), b4, b5, b6, b7, b8, b9]) ∗ ((S - 320#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ a0), (((b1 ^^^ a1) &&& t260) ^^^ a1), (((b2 ^^^ a2) &&& t260) ^^^ a2), (((b3 ^^^ a3) &&& t260) ^^^ a3), (((b4 ^^^ a4) &&& t260) ^^^ a4), (((b5 ^^^ a5) &&& t260) ^^^ a5), a6, a7, a8, a9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ F := hs14
  replace kf15 := kf12.trans kf15
  clear hs11 kf12
  refine x_eor (d := 8#5) (a := 18#5) (b := 15#5) (x := ((b4 ^^^ a4) &&& t260)) (y := b4) (by decide) (by decide) (by decide) hrun252 (c15_424 hP hCL 15 kf15) (pc4 _ 424 428 rfl) rfl rfl (fun t424 e424 => ?_)
  subst e424
  refine x_eor (d := 9#5) (a := 24#5) (b := 16#5) (x := ((b5 ^^^ a5) &&& t260)) (y := b5) (by decide) (by decide) (by decide) hrun252 (c15_428 hP hCL 15 kf15) (pc4 _ 428 432 rfl) rfl rfl (fun t428 e428 => ?_)
  subst e428
  refine x_eor (d := 23#5) (a := 27#5) (b := 23#5) (x := ((b6 ^^^ a6) &&& t260)) (y := a6) (by decide) (by decide) (by decide) hrun252 (c15_432 hP hCL 15 kf15) (pc4 _ 432 436 rfl) rfl rfl (fun t432 e432 => ?_)
  subst e432
  refine x_eor (d := 3#5) (a := 5#5) (b := 3#5) (x := ((b7 ^^^ a7) &&& t260)) (y := a7) (by decide) (by decide) (by decide) hrun252 (c15_436 hP hCL 15 kf15) (pc4 _ 436 440 rfl) rfl rfl (fun t436 e436 => ?_)
  subst e436
  refine x_eor (d := 6#5) (a := 26#5) (b := 4#5) (x := b8) (y := a8) (by decide) (by decide) (by decide) hrun252 (c15_440 hP hCL 15 kf15) (pc4 _ 440 444 rfl) rfl rfl (fun t440 e440 => ?_)
  subst e440
  refine x_eor (d := 7#5) (a := 25#5) (b := 1#5) (x := b9) (y := a9) (by decide) (by decide) (by decide) hrun252 (c15_444 hP hCL 15 kf15) (pc4 _ 444 448 rfl) rfl rfl (fun t444 e444 => ?_)
  subst e444
  refine x_stp_sp (t1 := 8#5) (t2 := 9#5) (v1 := (((b4 ^^^ a4) &&& t260) ^^^ b4)) (v2 := (((b5 ^^^ a5) &&& t260) ^^^ b5)) (i := 4) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_448 hP hCL 15 kf15) (pc4 _ 448 452 rfl) (aSS S 368 160 240 (8 * 4) (by decide)) hs14 (by exact (by decide : 5 < 10)) rfl rfl (fun m16 hs17 kf18 => ?_)
  replace hs17 : m16 ⊨ ((S - 240#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ b0), (((b1 ^^^ a1) &&& t260) ^^^ b1), (((b2 ^^^ a2) &&& t260) ^^^ b2), (((b3 ^^^ a3) &&& t260) ^^^ b3), (((b4 ^^^ a4) &&& t260) ^^^ b4), (((b5 ^^^ a5) &&& t260) ^^^ b5), b6, b7, b8, b9]) ∗ ((S - 320#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ a0), (((b1 ^^^ a1) &&& t260) ^^^ a1), (((b2 ^^^ a2) &&& t260) ^^^ a2), (((b3 ^^^ a3) &&& t260) ^^^ a3), (((b4 ^^^ a4) &&& t260) ^^^ a4), (((b5 ^^^ a5) &&& t260) ^^^ a5), a6, a7, a8, a9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ F := hs17
  replace kf18 := kf15.trans kf18
  clear hs14 kf15
  refine x_and (d := 6#5) (a := 6#5) (b := 10#5) (x := (b8 ^^^ a8)) (y := t260) (by decide) (by decide) (by decide) hrun252 (c15_452 hP hCL 15 kf18) (pc4 _ 452 456 rfl) rfl rfl (fun t452 e452 => ?_)
  subst e452
  refine x_and (d := 10#5) (a := 7#5) (b := 10#5) (x := (b9 ^^^ a9)) (y := t260) (by decide) (by decide) (by decide) hrun252 (c15_456 hP hCL 15 kf18) (pc4 _ 456 460 rfl) rfl rfl (fun t456 e456 => ?_)
  subst e456
  refine x_eor (d := 8#5) (a := 27#5) (b := 0#5) (x := ((b6 ^^^ a6) &&& t260)) (y := b6) (by decide) (by decide) (by decide) hrun252 (c15_460 hP hCL 15 kf18) (pc4 _ 460 464 rfl) rfl rfl (fun t460 e460 => ?_)
  subst e460
  refine x_eor (d := 4#5) (a := 6#5) (b := 4#5) (x := ((b8 ^^^ a8) &&& t260)) (y := a8) (by decide) (by decide) (by decide) hrun252 (c15_464 hP hCL 15 kf18) (pc4 _ 464 468 rfl) rfl rfl (fun t464 e464 => ?_)
  subst e464
  refine x_eor (d := 1#5) (a := 10#5) (b := 1#5) (x := ((b9 ^^^ a9) &&& t260)) (y := a9) (by decide) (by decide) (by decide) hrun252 (c15_468 hP hCL 15 kf18) (pc4 _ 468 472 rfl) rfl rfl (fun t468 e468 => ?_)
  subst e468
  refine x_eor (d := 9#5) (a := 5#5) (b := 28#5) (x := ((b7 ^^^ a7) &&& t260)) (y := b7) (by decide) (by decide) (by decide) hrun252 (c15_472 hP hCL 15 kf18) (pc4 _ 472 476 rfl) rfl rfl (fun t472 e472 => ?_)
  subst e472
  rw [pick2] at hs17
  refine x_stp_sp (t1 := 4#5) (t2 := 1#5) (v1 := (((b8 ^^^ a8) &&& t260) ^^^ a8)) (v2 := (((b9 ^^^ a9) &&& t260) ^^^ a9)) (i := 8) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_476 hP hCL 15 kf18) (pc4 _ 476 480 rfl) (aSS S 368 112 320 (8 * 8) (by decide)) hs17 (by exact (by decide : 9 < 10)) rfl rfl (fun m19 hs20 kf21 => ?_)
  replace hs20 : m19 ⊨ ((S - 320#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ a0), (((b1 ^^^ a1) &&& t260) ^^^ a1), (((b2 ^^^ a2) &&& t260) ^^^ a2), (((b3 ^^^ a3) &&& t260) ^^^ a3), (((b4 ^^^ a4) &&& t260) ^^^ a4), (((b5 ^^^ a5) &&& t260) ^^^ a5), a6, a7, (((b8 ^^^ a8) &&& t260) ^^^ a8), (((b9 ^^^ a9) &&& t260) ^^^ a9)]) ∗ ((S - 240#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ b0), (((b1 ^^^ a1) &&& t260) ^^^ b1), (((b2 ^^^ a2) &&& t260) ^^^ b2), (((b3 ^^^ a3) &&& t260) ^^^ b3), (((b4 ^^^ a4) &&& t260) ^^^ b4), (((b5 ^^^ a5) &&& t260) ^^^ b5), b6, b7, b8, b9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ F := hs20
  replace kf21 := kf18.trans kf21
  clear hs17 kf18
  refine x_addi_sp2 (d := 0#5) (by decide) hrun252 (c15_480 hP hCL 15 kf21) (pc4 _ 480 484 rfl) (aSk S 368 320 _ (by decide)) ?_
  refine x_addi_sp2 (d := 1#5) (by decide) hrun252 (c15_484 hP hCL 15 kf21) (pc4 _ 484 488 rfl) (aSk S 368 240 _ (by decide)) ?_
  rw [pick2] at hs20
  refine x_stp_sp (t1 := 8#5) (t2 := 9#5) (v1 := (((b6 ^^^ a6) &&& t260) ^^^ b6)) (v2 := (((b7 ^^^ a7) &&& t260) ^^^ b7)) (i := 6) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_488 hP hCL 15 kf21) (pc4 _ 488 492 rfl) (aSS S 368 176 240 (8 * 6) (by decide)) hs20 (by exact (by decide : 7 < 10)) rfl rfl (fun m22 hs23 kf24 => ?_)
  replace hs23 : m22 ⊨ ((S - 240#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ b0), (((b1 ^^^ a1) &&& t260) ^^^ b1), (((b2 ^^^ a2) &&& t260) ^^^ b2), (((b3 ^^^ a3) &&& t260) ^^^ b3), (((b4 ^^^ a4) &&& t260) ^^^ b4), (((b5 ^^^ a5) &&& t260) ^^^ b5), (((b6 ^^^ a6) &&& t260) ^^^ b6), (((b7 ^^^ a7) &&& t260) ^^^ b7), b8, b9]) ∗ ((S - 320#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ a0), (((b1 ^^^ a1) &&& t260) ^^^ a1), (((b2 ^^^ a2) &&& t260) ^^^ a2), (((b3 ^^^ a3) &&& t260) ^^^ a3), (((b4 ^^^ a4) &&& t260) ^^^ a4), (((b5 ^^^ a5) &&& t260) ^^^ a5), a6, a7, (((b8 ^^^ a8) &&& t260) ^^^ a8), (((b9 ^^^ a9) &&& t260) ^^^ a9)]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ F := hs23
  replace kf24 := kf21.trans kf24
  clear hs20 kf21
  refine x_eor (d := 8#5) (a := 6#5) (b := 26#5) (x := ((b8 ^^^ a8) &&& t260)) (y := b8) (by decide) (by decide) (by decide) hrun252 (c15_492 hP hCL 15 kf24) (pc4 _ 492 496 rfl) rfl rfl (fun t492 e492 => ?_)
  subst e492
  refine x_eor (d := 9#5) (a := 10#5) (b := 25#5) (x := ((b9 ^^^ a9) &&& t260)) (y := b9) (by decide) (by decide) (by decide) hrun252 (c15_496 hP hCL 15 kf24) (pc4 _ 496 500 rfl) rfl rfl (fun t496 e496 => ?_)
  subst e496
  refine x_addi_sp2 (d := 2#5) (by decide) hrun252 (c15_500 hP hCL 15 kf24) (pc4 _ 500 504 rfl) (aSk S 368 360 _ (by decide)) ?_
  rw [pick2] at hs23
  refine x_stp_sp (t1 := 23#5) (t2 := 3#5) (v1 := (((b6 ^^^ a6) &&& t260) ^^^ a6)) (v2 := (((b7 ^^^ a7) &&& t260) ^^^ a7)) (i := 6) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_504 hP hCL 15 kf24) (pc4 _ 504 508 rfl) (aSS S 368 96 320 (8 * 6) (by decide)) hs23 (by exact (by decide : 7 < 10)) rfl rfl (fun m25 hs26 kf27 => ?_)
  replace hs26 : m25 ⊨ ((S - 320#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ a0), (((b1 ^^^ a1) &&& t260) ^^^ a1), (((b2 ^^^ a2) &&& t260) ^^^ a2), (((b3 ^^^ a3) &&& t260) ^^^ a3), (((b4 ^^^ a4) &&& t260) ^^^ a4), (((b5 ^^^ a5) &&& t260) ^^^ a5), (((b6 ^^^ a6) &&& t260) ^^^ a6), (((b7 ^^^ a7) &&& t260) ^^^ a7), (((b8 ^^^ a8) &&& t260) ^^^ a8), (((b9 ^^^ a9) &&& t260) ^^^ a9)]) ∗ ((S - 240#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ b0), (((b1 ^^^ a1) &&& t260) ^^^ b1), (((b2 ^^^ a2) &&& t260) ^^^ b2), (((b3 ^^^ a3) &&& t260) ^^^ b3), (((b4 ^^^ a4) &&& t260) ^^^ b4), (((b5 ^^^ a5) &&& t260) ^^^ b5), (((b6 ^^^ a6) &&& t260) ^^^ b6), (((b7 ^^^ a7) &&& t260) ^^^ b7), b8, b9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ F := hs26
  replace kf27 := kf24.trans kf27
  clear hs23 kf24
  rw [pick2] at hs26
  refine x_stp_sp (t1 := 8#5) (t2 := 9#5) (v1 := (((b8 ^^^ a8) &&& t260) ^^^ b8)) (v2 := (((b9 ^^^ a9) &&& t260) ^^^ b9)) (i := 8) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun252 (c15_508 hP hCL 15 kf27) (pc4 _ 508 512 rfl) (aSS S 368 192 240 (8 * 8) (by decide)) hs26 (by exact (by decide : 9 < 10)) rfl rfl (fun m28 hs29 kf30 => ?_)
  replace hs29 : m28 ⊨ ((S - 240#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ b0), (((b1 ^^^ a1) &&& t260) ^^^ b1), (((b2 ^^^ a2) &&& t260) ^^^ b2), (((b3 ^^^ a3) &&& t260) ^^^ b3), (((b4 ^^^ a4) &&& t260) ^^^ b4), (((b5 ^^^ a5) &&& t260) ^^^ b5), (((b6 ^^^ a6) &&& t260) ^^^ b6), (((b7 ^^^ a7) &&& t260) ^^^ b7), (((b8 ^^^ a8) &&& t260) ^^^ b8), (((b9 ^^^ a9) &&& t260) ^^^ b9)]) ∗ ((S - 320#64) ↦₆₄* [(((b0 ^^^ a0) &&& t260) ^^^ a0), (((b1 ^^^ a1) &&& t260) ^^^ a1), (((b2 ^^^ a2) &&& t260) ^^^ a2), (((b3 ^^^ a3) &&& t260) ^^^ a3), (((b4 ^^^ a4) &&& t260) ^^^ a4), (((b5 ^^^ a5) &&& t260) ^^^ a5), (((b6 ^^^ a6) &&& t260) ^^^ a6), (((b7 ^^^ a7) &&& t260) ^^^ a7), (((b8 ^^^ a8) &&& t260) ^^^ a8), (((b9 ^^^ a9) &&& t260) ^^^ a9)]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ F := hs29
  replace kf30 := kf27.trans kf30
  clear hs26 kf27
  rw [pick3] at hs29
  rw [pick2] at hs29
  rw [pick3] at hs29
  rw [pick6] at hs29
  rw [pick5] at hs29
  have hm : t260 = 0#64 - BitVec.setWidth 64 (BitVec.setWidth 8 (sf252.regs.regs 0#5)) := e260
  have hc8 := bb_mask _ bit sv hbit hsv (by rw [hx252, upd_same, e248])
  have hL : ∀ wa wb : BitVec 64, ((wb ^^^ wa) &&& t260) ^^^ wa = if bit = sv then wa else wb :=
    fun wa wb => by rw [hm, hc8]; exact cswapL wa wb _
  have hR : ∀ wa wb : BitVec 64, ((wb ^^^ wa) &&& t260) ^^^ wb = if bit = sv then wb else wa :=
    fun wa wb => by rw [hm, hc8]; exact cswapR wa wb _
  simp only [hL, hR] at hs29
  rw [ite10, ite10] at hs29
  have hPb := montb_ite (c := bit = sv) hA hB
  have hQb := montb_ite (c := bit = sv) hB hA
  refine call_dad15 hP 15 hCL hrun252 kf30 (aligned_sub hal 368 (by decide) (by decide)) (c15_512 hP hCL 15 kf30 lk_dad) (pc4 _ 512 516 rfl) rfl rfl rfl hs29 hPb hQb hUb (fun sf512 R0 R1 hrun512 kf512 hv512 hl0 hl1 hb0 hb1 hv0 hv1 hs512 => ?_)
  have hvs512 : VRegFile.calleeSaved ⟨sf512.vregs.regs⟩ = VRegFile.calleeSaved ⟨vo⟩ := hv512.trans hvs252
  rw [pick6] at hs512
  refine x_strb_u (t := 22#5) (b := 29#5) (x := (S - 96#64)) (vb := BitVec.ofNat 64 bit) (by decide) (by decide) hrun512 (c15_516 hP hCL 15 kf512) (pc4 _ 516 520 rfl) rfl (aSb S 96 18446744073709551564 148 (by decide)) hs512 rfl (fun m31 hs32 kf33 => ?_)
  replace hs32 : m31 ⊨ ((S - 148#64) ↦ₛ [(BitVec.ofNat 64 bit).setWidth 8]) ∗ ((S - 360#64) ↦₆₄* [uw0, uw1, uw2, uw3, uw4]) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ ((S - 320#64) ↦₆₄* R0) ∗ ((S - 240#64) ↦₆₄* R1) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ F := hs32
  replace kf33 := kf512.trans kf33
  clear hs512 kf512
  refine x_movw (d := 0#5) (b := 22#5) (y := BitVec.ofNat 64 bit) (by decide) (by decide) hrun512 (c15_520 hP hCL 15 kf33) (pc4 _ 520 524 rfl) rfl (fun t520 e520 => ?_)
  refine x_cbz_t (t := 20#5) (x := 0#64) (by decide) hrun512 (c15_524 hP hCL 15 kf33) rfl (by decide) (pcb _ 524 18446744073709551284 192 (by decide)) ?_
  exact hcont _ _ _ _ _ R0 R1 hrun512 kf33 hvs512 rfl rfl rfl (by show t520 = _; rw [e520]; exact sw_ofNat_lt bit hbit)
    hl0 hl1 hb0 hb1 hv0 hv1 (Satisfies.of_eq hs32 (by ac_rfl))

end X25519Dalek.LP

end
end

section
section
/-! # Block 15, offsets 192–244: the iterator step and the scalar bit (generated by `tools_ladder/mk_b15head.py`) -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj

set_option maxHeartbeats 4000000 in
theorem b15_head {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {S out sc : BitVec 64} {F : SepProp} {Q : State → Prop}
    {vo : BitVec 5 → BitVec 128} {sbs : List (BitVec 8)} (hsl : sbs.length = 32) (hal : (S &&& 15#64 == 0#64) = true)
    {j sv : Nat} (hj : j < 254)
    {sb : State} {r : BitVec 5 → BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    (hrun : sb.status = .Running) (kf : m0.KeepsFrozen m)
    (hvs : VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨vo⟩)
    (hr19 : r 19#5 = out) (hr21 : r 21#5 = 0#64) (hr29 : r 29#5 = S - 96#64) (hr0 : r 0#5 = BitVec.ofNat 64 sv)
    (hs : m ⊨ ((S - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 (j + 1)]) ∗ (sc ↦ₛ sbs) ∗ F)
    (hcont : ∀ (sb' : State) (r' : BitVec 5 → BitVec 64) (ps' : PState) (m' : Memory) (v' : BitVec 5 → BitVec 128),
      sb'.status = .Running → m0.KeepsFrozen m' → VRegFile.calleeSaved ⟨v'⟩ = VRegFile.calleeSaved ⟨vo⟩ →
      r' 19#5 = out → r' 20#5 = 0#64 → r' 21#5 = 0#64 → r' 22#5 = BitVec.ofNat 64 (leBytesToNat sbs / 2 ^ j % 2) →
      r' 29#5 = S - 96#64 → r' 0#5 = BitVec.ofNat 64 sv →
      (m' ⊨ ((S - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 j]) ∗ (sc ↦ₛ sbs) ∗ F) →
      Reach (bprog mpl 15) (mkS sb' (mpl.base 15 + BitVec.ofNat 64 248) r' (S - 368#64) ps' m' v') Q) :
    Reach (bprog mpl 15) (mkS sb (mpl.base 15 + BitVec.ofNat 64 192) r (S - 368#64) ps m v) Q := by
  refine reach_reg (i := 19#5) hr19 ?_
  refine reach_reg (i := 21#5) hr21 ?_
  refine reach_reg (i := 29#5) hr29 ?_
  refine reach_reg (i := 0#5) hr0 ?_
  refine x_ldp_r (d1 := 8#5) (d2 := 10#5) (b := 29#5) (x := (S - 96#64)) (a := (S - 144#64)) (i := 1) (by decide) (by decide) (by decide) hrun (c15_192 hP hCL 15 kf) (pc4 _ 192 196 rfl) rfl (aSS S 96 18446744073709551576 144 (8 * 1) (by decide)) (wf1 hs 1 (by exact (by decide : 1 < 3)) : m.read64 _ = 0#64 ∧ _) rfl (wf1 hs 2 (by exact (by decide : 2 < 3)) : m.read64 _ = BitVec.ofNat 64 (j + 1) ∧ _) ?_
  refine x_cmp (a := 8#5) (b := 10#5) (x := 0#64) (y := BitVec.ofNat 64 (j + 1)) (by decide) (by decide) hrun (c15_196 hP hCL 15 kf) (pc4 _ 196 200 rfl) rfl rfl ?_
  have hc200 := head_cs200 j hj
  refine x_bcond_n hrun (c15_200 hP hCL 15 kf) hc200 (pc4 _ 200 204 rfl) ?_
  refine x_subi (d := 9#5) (a := 10#5) (x := BitVec.ofNat 64 (j + 1)) (by decide) (by decide) hrun (c15_204 hP hCL 15 kf) (pc4 _ 204 208 rfl) rfl (fun t204 e204 => ?_)
  have h204 : t204 = BitVec.ofNat 64 j := by rw [e204]; exact head_sub j hj
  refine x_cmpi (a := 10#5) (x := BitVec.ofNat 64 (j + 1)) (by decide) hrun (c15_208 hP hCL 15 kf) (pc4 _ 208 212 rfl) rfl ?_
  refine x_ubfm (d := 8#5) (a := 9#5) (i := 3) (j := 63) (x := t204) (by decide) (by decide) hrun (c15_212 hP hCL 15 kf) (pc4 _ 212 216 rfl) rfl (fun t212 e212 => ?_)
  have h212 : t212 = BitVec.ofNat 64 (j / 8) := by rw [e212, h204]; exact head_shr j hj
  refine x_str_r (t := 9#5) (b := 29#5) (x := (S - 96#64)) (v1 := t204) (i := 2) (by decide) (by decide) hrun (c15_216 hP hCL 15 kf) (pc4 _ 216 220 rfl) rfl (aSS S 96 18446744073709551584 144 (8 * 2) (by decide)) hs (by exact (by decide : 2 < 3)) rfl (fun m1 hs2 kf3 => ?_)
  replace hs2 : m1 ⊨ ((S - 144#64) ↦₆₄* [sc, 0#64, t204]) ∗ (sc ↦ₛ sbs) ∗ F := hs2
  replace kf3 := kf.trans kf3
  clear hs kf
  have hc220 := head_cs220 j hj
  refine x_bcond_n hrun (c15_220 hP hCL 15 kf3) hc220 (pc4 _ 220 224 rfl) ?_
  refine x_ldr_u (d := 10#5) (b := 29#5) (x := (S - 96#64)) (a := (S - 144#64)) (i := 0) (by decide) (by decide) hrun (c15_224 hP hCL 15 kf3) (pc4 _ 224 228 rfl) rfl (aSS S 96 18446744073709551568 144 (8 * 0) (by decide)) (wf1 hs2 0 (by exact (by decide : 0 < 3)) : m1.read64 _ = sc ∧ _) ?_
  refine x_andi (d := 9#5) (a := 9#5) (x := t204) (by decide) (by decide) hrun (c15_228 hP hCL 15 kf3) (pc4 _ 228 232 rfl) rfl (fun t228 e228 => ?_)
  have h228 : t228 = BitVec.ofNat 64 (j % 8) := by rw [e228, h204]; exact head_and7 j hj
  refine x_movzr64 (d := 20#5) (by decide) hrun (c15_232 hP hCL 15 kf3) (pc4 _ 232 236 rfl) ?_
  rw [pick2] at hs2
  refine x_ldrb_reg (d := 8#5) (b := 10#5) (i := 8#5) (x := sc) (y := t212) (by decide) (by decide) (by decide) hrun (c15_236 hP hCL 15 kf3) (pc4 _ 236 240 rfl) rfl rfl rfl (byte_at hs2 t212 (j / 8) h212 (by rw [hsl]; omega)) ?_
  refine x_lsrvw (d := 8#5) (a := 8#5) (b := 9#5) (x := (((sbs.getD (j / 8) 0).setWidth 64).setWidth 32).setWidth 64) (y := t228) (by decide) (by decide) (by decide) hrun (c15_240 hP hCL 15 kf3) (pc4 _ 240 244 rfl) rfl rfl (fun t240 e240 => ?_)
  refine x_andiw (d := 22#5) (a := 8#5) (x := t240) (by decide) (by decide) hrun (c15_244 hP hCL 15 kf3) (pc4 _ 244 248 rfl) rfl (fun t244 e244 => ?_)
  have h244 : t244 = BitVec.ofNat 64 (leBytesToNat sbs / 2 ^ j % 2) := by
    rw [e244, e240, h228, head_bit _ _ (by omega)]; exact congrArg _ (scalar_bit sbs j)
  rw [h204] at hs2
  exact hcont _ _ _ _ _ hrun kf3 hvs rfl rfl rfl (by show t244 = _; exact h244) rfl rfl (Satisfies.of_eq hs2 (by ac_rfl))

end X25519Dalek.LP

end
end

section
section
/-! # Block 15, offsets 192–200 and 576–820: the last select, `as_affine`, the epilogue
(generated by `tools_ladder/mk_b15exit.py`) -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj

set_option maxHeartbeats 8000000 in
theorem b15_exit {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {S out sc : BitVec 64} {F : SepProp} {Q : State → Prop}
    {vo : BitVec 5 → BitVec 128} (hal : (S &&& 15#64 == 0#64) = true)
    {c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 : BitVec 64}
    {sb : State} {r : BitVec 5 → BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 64} {bb : BitVec 8}
    {ob : List (BitVec 8)} (hol : ob.length = 32) {sv : Nat} (hsv : sv < 2)
    (hrun : sb.status = .Running) (kf : m0.KeepsFrozen m)
    (hvs : VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨vo⟩)
    (hr19 : r 19#5 = out) (hr21 : r 21#5 = 0#64) (hr29 : r 29#5 = S - 96#64) (hr0 : r 0#5 = BitVec.ofNat 64 sv)
    (hA : montProjBounded ([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].flatMap unpack64) (2 ^ 52))
    (hB : montProjBounded ([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9].flatMap unpack64) (2 ^ 52))
    (hs : m ⊨ ((S - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 0]) ∗ ((S - 320#64) ↦₆₄* [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]) ∗
      ((S - 240#64) ↦₆₄* [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗
      memRegion ((S - 368#64) - 1312#64) 1312 ∗ (out ↦ₛ ob) ∗ F)
    (hcont : ∀ (sb' : State) (r' : BitVec 5 → BitVec 64) (ps' : PState) (m' : Memory) (v' : BitVec 5 → BitVec 128),
      sb'.status = .Running → m0.KeepsFrozen m' → VRegFile.calleeSaved ⟨v'⟩ = VRegFile.calleeSaved ⟨vo⟩ →
      r' 19#5 = c19 → r' 20#5 = c20 → r' 21#5 = c21 → r' 22#5 = c22 → r' 23#5 = c23 → r' 24#5 = c24 →
      r' 25#5 = c25 → r' 26#5 = c26 → r' 27#5 = c27 → r' 28#5 = c28 → r' 29#5 = c29 →
      (m' ⊨ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ ((S - 320#64) ↦₆₄* (if sv = 1 then [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] else [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9])) ∗
        (out ↦ₛ natToLeBytes 32 (fpMul (montProjOfBytes ((if sv = 1 then [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] else [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]).flatMap unpack64)).U
          (fpInv (montProjOfBytes ((if sv = 1 then [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] else [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]).flatMap unpack64)).W))) ∗
        memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 148#64) ↦ₛ [0#8]) ∗ ((S - 240#64) ↦₆₄* [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]) ∗
        ((S - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 0]) ∗ F) →
      Reach (bprog mpl 15) (mkS sb' c30 r' (S - 0#64) ps' m' v') Q) :
    Reach (bprog mpl 15) (mkS sb (mpl.base 15 + BitVec.ofNat 64 192) r (S - 368#64) ps m v) Q := by
  refine reach_reg (i := 19#5) hr19 ?_
  refine reach_reg (i := 21#5) hr21 ?_
  refine reach_reg (i := 29#5) hr29 ?_
  refine reach_reg (i := 0#5) hr0 ?_
  refine x_ldp_r (d1 := 8#5) (d2 := 10#5) (b := 29#5) (x := (S - 96#64)) (a := (S - 144#64)) (i := 1) (by decide) (by decide) (by decide) hrun (c15_192 hP hCL 15 kf) (pc4 _ 192 196 rfl) rfl (aSS S 96 18446744073709551576 144 (8 * 1) (by decide)) (wf1 hs 1 (by exact (by decide : 1 < 3)) : m.read64 _ = 0#64 ∧ _) rfl (wf1 hs 2 (by exact (by decide : 2 < 3)) : m.read64 _ = BitVec.ofNat 64 0 ∧ _) ?_
  refine x_cmp (a := 8#5) (b := 10#5) (x := 0#64) (y := BitVec.ofNat 64 0) (by decide) (by decide) hrun (c15_196 hP hCL 15 kf) (pc4 _ 196 200 rfl) rfl rfl ?_
  have hc200 := exit_cs200
  refine x_bcond_t hrun (c15_200 hP hCL 15 kf) hc200 (pcb _ 200 376 576 (by decide)) ?_
  rw [pick6] at hs
  refine call_bb15 hP 15 hCL hrun kf (aligned_sub hal 368 (by decide) (by decide)) (c15_576 hP hCL 15 kf lk_bb) (pc4 _ 576 580 rfl) hs (fun sf576 hrun576 kf576 hv576 hx576 hs576 => ?_)
  have hvs576 : VRegFile.calleeSaved ⟨sf576.vregs.regs⟩ = VRegFile.calleeSaved ⟨vo⟩ := hv576.trans hvs
  rw [pick3] at hs576
  refine x_ldp_sp (d1 := 10#5) (d2 := 11#5) (a := (S - 320#64)) (i := 0) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun576 (c15_580 hP hCL 15 kf576) (pc4 _ 580 584 rfl) (aSS S 368 48 320 (8 * 0) (by decide)) (wf1 hs576 0 (by exact (by decide : 0 < 10)) : sf576.mem.read64 _ = a0 ∧ _) rfl (wf1 hs576 1 (by exact (by decide : 1 < 10)) : sf576.mem.read64 _ = a1 ∧ _) ?_
  refine x_andi (d := 9#5) (a := 0#5) (x := sf576.regs.regs 0#5) (by decide) (by decide) hrun576 (c15_584 hP hCL 15 kf576) (pc4 _ 584 588 rfl) rfl (fun t584 e584 => ?_)
  rw [pick4] at hs576
  refine x_ldp_sp (d1 := 16#5) (d2 := 17#5) (a := (S - 240#64)) (i := 0) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun576 (c15_588 hP hCL 15 kf576) (pc4 _ 588 592 rfl) (aSS S 368 128 240 (8 * 0) (by decide)) (wf1 hs576 0 (by exact (by decide : 0 < 10)) : sf576.mem.read64 _ = b0 ∧ _) rfl (wf1 hs576 1 (by exact (by decide : 1 < 10)) : sf576.mem.read64 _ = b1 ∧ _) ?_
  refine x_neg (d := 8#5) (b := 9#5) (y := t584) (by decide) (by decide) hrun576 (c15_592 hP hCL 15 kf576) (pc4 _ 592 596 rfl) rfl (fun t592 e592 => ?_)
  rw [pick2] at hs576
  refine x_ldp_sp (d1 := 12#5) (d2 := 13#5) (a := (S - 320#64)) (i := 2) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun576 (c15_596 hP hCL 15 kf576) (pc4 _ 596 600 rfl) (aSS S 368 64 320 (8 * 2) (by decide)) (wf1 hs576 2 (by exact (by decide : 2 < 10)) : sf576.mem.read64 _ = a2 ∧ _) rfl (wf1 hs576 3 (by exact (by decide : 3 < 10)) : sf576.mem.read64 _ = a3 ∧ _) ?_
  refine x_subi (d := 9#5) (a := 9#5) (x := t584) (by decide) (by decide) hrun576 (c15_600 hP hCL 15 kf576) (pc4 _ 600 604 rfl) rfl (fun t600 e600 => ?_)
  rw [pick2] at hs576
  refine x_ldp_sp (d1 := 1#5) (d2 := 2#5) (a := (S - 240#64)) (i := 2) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun576 (c15_604 hP hCL 15 kf576) (pc4 _ 604 608 rfl) (aSS S 368 144 240 (8 * 2) (by decide)) (wf1 hs576 2 (by exact (by decide : 2 < 10)) : sf576.mem.read64 _ = b2 ∧ _) rfl (wf1 hs576 3 (by exact (by decide : 3 < 10)) : sf576.mem.read64 _ = b3 ∧ _) ?_
  refine x_and (d := 10#5) (a := 10#5) (b := 9#5) (x := a0) (y := t600) (by decide) (by decide) (by decide) hrun576 (c15_608 hP hCL 15 kf576) (pc4 _ 608 612 rfl) rfl rfl (fun t608 e608 => ?_)
  subst e608
  refine x_and (d := 16#5) (a := 16#5) (b := 8#5) (x := b0) (y := t592) (by decide) (by decide) (by decide) hrun576 (c15_612 hP hCL 15 kf576) (pc4 _ 612 616 rfl) rfl rfl (fun t612 e612 => ?_)
  subst e612
  refine x_and (d := 11#5) (a := 11#5) (b := 9#5) (x := a1) (y := t600) (by decide) (by decide) (by decide) hrun576 (c15_616 hP hCL 15 kf576) (pc4 _ 616 620 rfl) rfl rfl (fun t616 e616 => ?_)
  subst e616
  refine x_and (d := 17#5) (a := 17#5) (b := 8#5) (x := b1) (y := t592) (by decide) (by decide) (by decide) hrun576 (c15_620 hP hCL 15 kf576) (pc4 _ 620 624 rfl) rfl rfl (fun t620 e620 => ?_)
  subst e620
  refine x_orr (d := 10#5) (a := 16#5) (b := 10#5) (x := (b0 &&& t592)) (y := (a0 &&& t600)) (by decide) (by decide) (by decide) hrun576 (c15_624 hP hCL 15 kf576) (pc4 _ 624 628 rfl) rfl rfl (fun t624 e624 => ?_)
  subst e624
  refine x_and (d := 13#5) (a := 13#5) (b := 9#5) (x := a3) (y := t600) (by decide) (by decide) (by decide) hrun576 (c15_628 hP hCL 15 kf576) (pc4 _ 628 632 rfl) rfl rfl (fun t628 e628 => ?_)
  subst e628
  refine x_orr (d := 11#5) (a := 17#5) (b := 11#5) (x := (b1 &&& t592)) (y := (a1 &&& t600)) (by decide) (by decide) (by decide) hrun576 (c15_632 hP hCL 15 kf576) (pc4 _ 632 636 rfl) rfl rfl (fun t632 e632 => ?_)
  subst e632
  refine x_and (d := 16#5) (a := 2#5) (b := 8#5) (x := b3) (y := t592) (by decide) (by decide) (by decide) hrun576 (c15_636 hP hCL 15 kf576) (pc4 _ 636 640 rfl) rfl rfl (fun t636 e636 => ?_)
  subst e636
  rw [pick2] at hs576
  refine x_ldp_sp (d1 := 14#5) (d2 := 15#5) (a := (S - 320#64)) (i := 4) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun576 (c15_640 hP hCL 15 kf576) (pc4 _ 640 644 rfl) (aSS S 368 80 320 (8 * 4) (by decide)) (wf1 hs576 4 (by exact (by decide : 4 < 10)) : sf576.mem.read64 _ = a4 ∧ _) rfl (wf1 hs576 5 (by exact (by decide : 5 < 10)) : sf576.mem.read64 _ = a5 ∧ _) ?_
  refine x_orr (d := 13#5) (a := 16#5) (b := 13#5) (x := (b3 &&& t592)) (y := (a3 &&& t600)) (by decide) (by decide) (by decide) hrun576 (c15_644 hP hCL 15 kf576) (pc4 _ 644 648 rfl) rfl rfl (fun t644 e644 => ?_)
  subst e644
  rw [pick2] at hs576
  refine x_ldp_sp (d1 := 17#5) (d2 := 16#5) (a := (S - 240#64)) (i := 4) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun576 (c15_648 hP hCL 15 kf576) (pc4 _ 648 652 rfl) (aSS S 368 160 240 (8 * 4) (by decide)) (wf1 hs576 4 (by exact (by decide : 4 < 10)) : sf576.mem.read64 _ = b4 ∧ _) rfl (wf1 hs576 5 (by exact (by decide : 5 < 10)) : sf576.mem.read64 _ = b5 ∧ _) ?_
  refine x_and (d := 12#5) (a := 12#5) (b := 9#5) (x := a2) (y := t600) (by decide) (by decide) (by decide) hrun576 (c15_652 hP hCL 15 kf576) (pc4 _ 652 656 rfl) rfl rfl (fun t652 e652 => ?_)
  subst e652
  refine x_and (d := 1#5) (a := 1#5) (b := 8#5) (x := b2) (y := t592) (by decide) (by decide) (by decide) hrun576 (c15_656 hP hCL 15 kf576) (pc4 _ 656 660 rfl) rfl rfl (fun t656 e656 => ?_)
  subst e656
  rw [pick2] at hs576
  refine x_stp_sp (t1 := 10#5) (t2 := 11#5) (v1 := ((b0 &&& t592) ||| (a0 &&& t600))) (v2 := ((b1 &&& t592) ||| (a1 &&& t600))) (i := 0) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun576 (c15_660 hP hCL 15 kf576) (pc4 _ 660 664 rfl) (aSS S 368 48 320 (8 * 0) (by decide)) hs576 (by exact (by decide : 1 < 10)) rfl rfl (fun m1 hs2 kf3 => ?_)
  replace hs2 : m1 ⊨ ((S - 320#64) ↦₆₄* [((b0 &&& t592) ||| (a0 &&& t600)), ((b1 &&& t592) ||| (a1 &&& t600)), a2, a3, a4, a5, a6, a7, a8, a9]) ∗ ((S - 240#64) ↦₆₄* [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 0]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ (out ↦ₛ ob) ∗ F := hs2
  replace kf3 := kf576.trans kf3
  clear hs576 kf576
  refine x_and (d := 14#5) (a := 14#5) (b := 9#5) (x := a4) (y := t600) (by decide) (by decide) (by decide) hrun576 (c15_664 hP hCL 15 kf3) (pc4 _ 664 668 rfl) rfl rfl (fun t664 e664 => ?_)
  subst e664
  refine x_and (d := 15#5) (a := 15#5) (b := 9#5) (x := a5) (y := t600) (by decide) (by decide) (by decide) hrun576 (c15_668 hP hCL 15 kf3) (pc4 _ 668 672 rfl) rfl rfl (fun t668 e668 => ?_)
  subst e668
  refine x_orr (d := 12#5) (a := 1#5) (b := 12#5) (x := (b2 &&& t592)) (y := (a2 &&& t600)) (by decide) (by decide) (by decide) hrun576 (c15_672 hP hCL 15 kf3) (pc4 _ 672 676 rfl) rfl rfl (fun t672 e672 => ?_)
  subst e672
  refine x_and (d := 17#5) (a := 17#5) (b := 8#5) (x := b4) (y := t592) (by decide) (by decide) (by decide) hrun576 (c15_676 hP hCL 15 kf3) (pc4 _ 676 680 rfl) rfl rfl (fun t676 e676 => ?_)
  subst e676
  refine x_and (d := 16#5) (a := 16#5) (b := 8#5) (x := b5) (y := t592) (by decide) (by decide) (by decide) hrun576 (c15_680 hP hCL 15 kf3) (pc4 _ 680 684 rfl) rfl rfl (fun t680 e680 => ?_)
  subst e680
  refine x_stp_sp (t1 := 12#5) (t2 := 13#5) (v1 := ((b2 &&& t592) ||| (a2 &&& t600))) (v2 := ((b3 &&& t592) ||| (a3 &&& t600))) (i := 2) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun576 (c15_684 hP hCL 15 kf3) (pc4 _ 684 688 rfl) (aSS S 368 64 320 (8 * 2) (by decide)) hs2 (by exact (by decide : 3 < 10)) rfl rfl (fun m4 hs5 kf6 => ?_)
  replace hs5 : m4 ⊨ ((S - 320#64) ↦₆₄* [((b0 &&& t592) ||| (a0 &&& t600)), ((b1 &&& t592) ||| (a1 &&& t600)), ((b2 &&& t592) ||| (a2 &&& t600)), ((b3 &&& t592) ||| (a3 &&& t600)), a4, a5, a6, a7, a8, a9]) ∗ ((S - 240#64) ↦₆₄* [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 0]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ (out ↦ₛ ob) ∗ F := hs5
  replace kf6 := kf3.trans kf6
  clear hs2 kf3
  refine x_orr (d := 14#5) (a := 17#5) (b := 14#5) (x := (b4 &&& t592)) (y := (a4 &&& t600)) (by decide) (by decide) (by decide) hrun576 (c15_688 hP hCL 15 kf6) (pc4 _ 688 692 rfl) rfl rfl (fun t688 e688 => ?_)
  subst e688
  refine x_orr (d := 15#5) (a := 16#5) (b := 15#5) (x := (b5 &&& t592)) (y := (a5 &&& t600)) (by decide) (by decide) (by decide) hrun576 (c15_692 hP hCL 15 kf6) (pc4 _ 692 696 rfl) rfl rfl (fun t692 e692 => ?_)
  subst e692
  refine x_ldp_sp (d1 := 18#5) (d2 := 0#5) (a := (S - 320#64)) (i := 6) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun576 (c15_696 hP hCL 15 kf6) (pc4 _ 696 700 rfl) (aSS S 368 96 320 (8 * 6) (by decide)) (wf1 hs5 6 (by exact (by decide : 6 < 10)) : m4.read64 _ = a6 ∧ _) rfl (wf1 hs5 7 (by exact (by decide : 7 < 10)) : m4.read64 _ = a7 ∧ _) ?_
  refine x_stp_sp (t1 := 14#5) (t2 := 15#5) (v1 := ((b4 &&& t592) ||| (a4 &&& t600))) (v2 := ((b5 &&& t592) ||| (a5 &&& t600))) (i := 4) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun576 (c15_700 hP hCL 15 kf6) (pc4 _ 700 704 rfl) (aSS S 368 80 320 (8 * 4) (by decide)) hs5 (by exact (by decide : 5 < 10)) rfl rfl (fun m7 hs8 kf9 => ?_)
  replace hs8 : m7 ⊨ ((S - 320#64) ↦₆₄* [((b0 &&& t592) ||| (a0 &&& t600)), ((b1 &&& t592) ||| (a1 &&& t600)), ((b2 &&& t592) ||| (a2 &&& t600)), ((b3 &&& t592) ||| (a3 &&& t600)), ((b4 &&& t592) ||| (a4 &&& t600)), ((b5 &&& t592) ||| (a5 &&& t600)), a6, a7, a8, a9]) ∗ ((S - 240#64) ↦₆₄* [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 0]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ (out ↦ₛ ob) ∗ F := hs8
  replace kf9 := kf6.trans kf9
  clear hs5 kf6
  refine x_ldp_sp (d1 := 1#5) (d2 := 2#5) (a := (S - 320#64)) (i := 8) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun576 (c15_704 hP hCL 15 kf9) (pc4 _ 704 708 rfl) (aSS S 368 112 320 (8 * 8) (by decide)) (wf1 hs8 8 (by exact (by decide : 8 < 10)) : m7.read64 _ = a8 ∧ _) rfl (wf1 hs8 9 (by exact (by decide : 9 < 10)) : m7.read64 _ = a9 ∧ _) ?_
  rw [pick2] at hs8
  refine x_ldp_sp (d1 := 17#5) (d2 := 10#5) (a := (S - 240#64)) (i := 6) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun576 (c15_708 hP hCL 15 kf9) (pc4 _ 708 712 rfl) (aSS S 368 176 240 (8 * 6) (by decide)) (wf1 hs8 6 (by exact (by decide : 6 < 10)) : m7.read64 _ = b6 ∧ _) rfl (wf1 hs8 7 (by exact (by decide : 7 < 10)) : m7.read64 _ = b7 ∧ _) ?_
  refine x_ldp_sp (d1 := 16#5) (d2 := 14#5) (a := (S - 240#64)) (i := 8) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun576 (c15_712 hP hCL 15 kf9) (pc4 _ 712 716 rfl) (aSS S 368 192 240 (8 * 8) (by decide)) (wf1 hs8 8 (by exact (by decide : 8 < 10)) : m7.read64 _ = b8 ∧ _) rfl (wf1 hs8 9 (by exact (by decide : 9 < 10)) : m7.read64 _ = b9 ∧ _) ?_
  refine x_and (d := 18#5) (a := 18#5) (b := 9#5) (x := a6) (y := t600) (by decide) (by decide) (by decide) hrun576 (c15_716 hP hCL 15 kf9) (pc4 _ 716 720 rfl) rfl rfl (fun t716 e716 => ?_)
  subst e716
  refine x_and (d := 12#5) (a := 0#5) (b := 9#5) (x := a7) (y := t600) (by decide) (by decide) (by decide) hrun576 (c15_720 hP hCL 15 kf9) (pc4 _ 720 724 rfl) rfl rfl (fun t720 e720 => ?_)
  subst e720
  refine x_and (d := 13#5) (a := 1#5) (b := 9#5) (x := a8) (y := t600) (by decide) (by decide) (by decide) hrun576 (c15_724 hP hCL 15 kf9) (pc4 _ 724 728 rfl) rfl rfl (fun t724 e724 => ?_)
  subst e724
  refine x_and (d := 9#5) (a := 2#5) (b := 9#5) (x := a9) (y := t600) (by decide) (by decide) (by decide) hrun576 (c15_728 hP hCL 15 kf9) (pc4 _ 728 732 rfl) rfl rfl (fun t728 e728 => ?_)
  subst e728
  refine x_and (d := 11#5) (a := 17#5) (b := 8#5) (x := b6) (y := t592) (by decide) (by decide) (by decide) hrun576 (c15_732 hP hCL 15 kf9) (pc4 _ 732 736 rfl) rfl rfl (fun t732 e732 => ?_)
  subst e732
  refine x_and (d := 10#5) (a := 10#5) (b := 8#5) (x := b7) (y := t592) (by decide) (by decide) (by decide) hrun576 (c15_736 hP hCL 15 kf9) (pc4 _ 736 740 rfl) rfl rfl (fun t736 e736 => ?_)
  subst e736
  refine x_addi_sp2 (d := 0#5) (by decide) hrun576 (c15_740 hP hCL 15 kf9) (pc4 _ 740 744 rfl) (aSk S 368 320 _ (by decide)) ?_
  refine x_and (d := 16#5) (a := 16#5) (b := 8#5) (x := b8) (y := t592) (by decide) (by decide) (by decide) hrun576 (c15_744 hP hCL 15 kf9) (pc4 _ 744 748 rfl) rfl rfl (fun t744 e744 => ?_)
  subst e744
  refine x_and (d := 8#5) (a := 14#5) (b := 8#5) (x := b9) (y := t592) (by decide) (by decide) (by decide) hrun576 (c15_748 hP hCL 15 kf9) (pc4 _ 748 752 rfl) rfl rfl (fun t748 e748 => ?_)
  subst e748
  refine x_orr (d := 11#5) (a := 11#5) (b := 18#5) (x := (b6 &&& t592)) (y := (a6 &&& t600)) (by decide) (by decide) (by decide) hrun576 (c15_752 hP hCL 15 kf9) (pc4 _ 752 756 rfl) rfl rfl (fun t752 e752 => ?_)
  subst e752
  refine x_orr (d := 10#5) (a := 10#5) (b := 12#5) (x := (b7 &&& t592)) (y := (a7 &&& t600)) (by decide) (by decide) (by decide) hrun576 (c15_756 hP hCL 15 kf9) (pc4 _ 756 760 rfl) rfl rfl (fun t756 e756 => ?_)
  subst e756
  refine x_orr (d := 12#5) (a := 16#5) (b := 13#5) (x := (b8 &&& t592)) (y := (a8 &&& t600)) (by decide) (by decide) (by decide) hrun576 (c15_760 hP hCL 15 kf9) (pc4 _ 760 764 rfl) rfl rfl (fun t760 e760 => ?_)
  subst e760
  refine x_orr (d := 8#5) (a := 8#5) (b := 9#5) (x := (b9 &&& t592)) (y := (a9 &&& t600)) (by decide) (by decide) (by decide) hrun576 (c15_764 hP hCL 15 kf9) (pc4 _ 764 768 rfl) rfl rfl (fun t764 e764 => ?_)
  subst e764
  rw [pick2] at hs8
  refine x_stp_sp (t1 := 11#5) (t2 := 10#5) (v1 := ((b6 &&& t592) ||| (a6 &&& t600))) (v2 := ((b7 &&& t592) ||| (a7 &&& t600))) (i := 6) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun576 (c15_768 hP hCL 15 kf9) (pc4 _ 768 772 rfl) (aSS S 368 96 320 (8 * 6) (by decide)) hs8 (by exact (by decide : 7 < 10)) rfl rfl (fun m10 hs11 kf12 => ?_)
  replace hs11 : m10 ⊨ ((S - 320#64) ↦₆₄* [((b0 &&& t592) ||| (a0 &&& t600)), ((b1 &&& t592) ||| (a1 &&& t600)), ((b2 &&& t592) ||| (a2 &&& t600)), ((b3 &&& t592) ||| (a3 &&& t600)), ((b4 &&& t592) ||| (a4 &&& t600)), ((b5 &&& t592) ||| (a5 &&& t600)), ((b6 &&& t592) ||| (a6 &&& t600)), ((b7 &&& t592) ||| (a7 &&& t600)), a8, a9]) ∗ ((S - 240#64) ↦₆₄* [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 0]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ (out ↦ₛ ob) ∗ F := hs11
  replace kf12 := kf9.trans kf12
  clear hs8 kf9
  refine x_stp_sp (t1 := 12#5) (t2 := 8#5) (v1 := ((b8 &&& t592) ||| (a8 &&& t600))) (v2 := ((b9 &&& t592) ||| (a9 &&& t600))) (i := 8) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun576 (c15_772 hP hCL 15 kf12) (pc4 _ 772 776 rfl) (aSS S 368 112 320 (8 * 8) (by decide)) hs11 (by exact (by decide : 9 < 10)) rfl rfl (fun m13 hs14 kf15 => ?_)
  replace hs14 : m13 ⊨ ((S - 320#64) ↦₆₄* [((b0 &&& t592) ||| (a0 &&& t600)), ((b1 &&& t592) ||| (a1 &&& t600)), ((b2 &&& t592) ||| (a2 &&& t600)), ((b3 &&& t592) ||| (a3 &&& t600)), ((b4 &&& t592) ||| (a4 &&& t600)), ((b5 &&& t592) ||| (a5 &&& t600)), ((b6 &&& t592) ||| (a6 &&& t600)), ((b7 &&& t592) ||| (a7 &&& t600)), ((b8 &&& t592) ||| (a8 &&& t600)), ((b9 &&& t592) ||| (a9 &&& t600))]) ∗ ((S - 240#64) ↦₆₄* [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 0]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ (out ↦ₛ ob) ∗ F := hs14
  replace kf15 := kf12.trans kf15
  clear hs11 kf12
  refine x_subi_r2 (d := 8#5) (a := 29#5) (by decide) (by decide) hrun576 (c15_776 hP hCL 15 kf15) (pc4 _ 776 780 rfl) rfl (aSmk S 96 148 _ (by decide)) ?_
  rw [pick5] at hs14
  refine x_strbzr_u (b := 29#5) (x := (S - 96#64)) (by decide) hrun576 (c15_780 hP hCL 15 kf15) (pc4 _ 780 784 rfl) rfl (aSb S 96 18446744073709551564 148 (by decide)) hs14 (fun m16 hs17 kf18 => ?_)
  replace hs17 : m16 ⊨ ((S - 148#64) ↦ₛ [0#8]) ∗ ((S - 320#64) ↦₆₄* [((b0 &&& t592) ||| (a0 &&& t600)), ((b1 &&& t592) ||| (a1 &&& t600)), ((b2 &&& t592) ||| (a2 &&& t600)), ((b3 &&& t592) ||| (a3 &&& t600)), ((b4 &&& t592) ||| (a4 &&& t600)), ((b5 &&& t592) ||| (a5 &&& t600)), ((b6 &&& t592) ||| (a6 &&& t600)), ((b7 &&& t592) ||| (a7 &&& t600)), ((b8 &&& t592) ||| (a8 &&& t600)), ((b9 &&& t592) ||| (a9 &&& t600))]) ∗ ((S - 240#64) ↦₆₄* [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 0]) ∗ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗ (out ↦ₛ ob) ∗ F := hs17
  replace kf18 := kf15.trans kf18
  clear hs14 kf15
  refine x_mov (d := 8#5) (b := 19#5) (y := out) (by decide) (by decide) hrun576 (c15_784 hP hCL 15 kf18) (pc4 _ 784 788 rfl) rfl ?_
  rw [pick4] at hs17
  rw [pick7] at hs17
  rw [pick4] at hs17
  have hsel : ∀ wa wb : BitVec 64, (wb &&& t592) ||| (wa &&& t600) = if sv = 1 then wb else wa := by
    intro wa wb; rw [e592, e600, e584]
    exact exit_sel _ sv hsv (by rw [hx576]; rfl) wa wb
  simp only [hsel] at hs17
  rw [ite10] at hs17
  have hSb := montb_ite (c := sv = 1) (montb_mono (b := 2 ^ 54) hB (Nat.pow_le_pow_right (by decide) (by decide))) (montb_mono (b := 2 ^ 54) hA (Nat.pow_le_pow_right (by decide) (by decide)))
  refine call_aa15 (out := out) (self := (S - 320#64)) hP 15 hCL hrun576 kf18 (aligned_sub hal 368 (by decide) (by decide)) (c15_788 hP hCL 15 kf18 lk_aa) (pc4 _ 788 792 rfl) rfl rfl hol hs17 hSb (fun sf788 hrun788 kf788 hv788 hs788 => ?_)
  have hvs788 : VRegFile.calleeSaved ⟨sf788.vregs.regs⟩ = VRegFile.calleeSaved ⟨vo⟩ := hv788.trans hvs576
  rw [pick7] at hs788
  refine x_ldp_sp (d1 := 20#5) (d2 := 19#5) (a := (S - 96#64)) (i := 10) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun788 (c15_792 hP hCL 15 kf788) (pc4 _ 792 796 rfl) (aSS S 368 352 96 (8 * 10) (by decide)) (wf1 hs788 10 (by exact (by decide : 10 < 12)) : sf788.mem.read64 _ = c20 ∧ _) rfl (wf1 hs788 11 (by exact (by decide : 11 < 12)) : sf788.mem.read64 _ = c19 ∧ _) ?_
  refine x_ldp_sp (d1 := 22#5) (d2 := 21#5) (a := (S - 96#64)) (i := 8) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun788 (c15_796 hP hCL 15 kf788) (pc4 _ 796 800 rfl) (aSS S 368 336 96 (8 * 8) (by decide)) (wf1 hs788 8 (by exact (by decide : 8 < 12)) : sf788.mem.read64 _ = c22 ∧ _) rfl (wf1 hs788 9 (by exact (by decide : 9 < 12)) : sf788.mem.read64 _ = c21 ∧ _) ?_
  refine x_ldp_sp (d1 := 24#5) (d2 := 23#5) (a := (S - 96#64)) (i := 6) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun788 (c15_800 hP hCL 15 kf788) (pc4 _ 800 804 rfl) (aSS S 368 320 96 (8 * 6) (by decide)) (wf1 hs788 6 (by exact (by decide : 6 < 12)) : sf788.mem.read64 _ = c24 ∧ _) rfl (wf1 hs788 7 (by exact (by decide : 7 < 12)) : sf788.mem.read64 _ = c23 ∧ _) ?_
  refine x_ldp_sp (d1 := 26#5) (d2 := 25#5) (a := (S - 96#64)) (i := 4) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun788 (c15_804 hP hCL 15 kf788) (pc4 _ 804 808 rfl) (aSS S 368 304 96 (8 * 4) (by decide)) (wf1 hs788 4 (by exact (by decide : 4 < 12)) : sf788.mem.read64 _ = c26 ∧ _) rfl (wf1 hs788 5 (by exact (by decide : 5 < 12)) : sf788.mem.read64 _ = c25 ∧ _) ?_
  refine x_ldp_sp (d1 := 28#5) (d2 := 27#5) (a := (S - 96#64)) (i := 2) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun788 (c15_808 hP hCL 15 kf788) (pc4 _ 808 812 rfl) (aSS S 368 288 96 (8 * 2) (by decide)) (wf1 hs788 2 (by exact (by decide : 2 < 12)) : sf788.mem.read64 _ = c28 ∧ _) rfl (wf1 hs788 3 (by exact (by decide : 3 < 12)) : sf788.mem.read64 _ = c27 ∧ _) ?_
  refine x_ldp_sp (d1 := 29#5) (d2 := 30#5) (a := (S - 96#64)) (i := 0) (by decide) (by decide) (aligned_sub hal 368 (by decide) (by decide)) hrun788 (c15_812 hP hCL 15 kf788) (pc4 _ 812 816 rfl) (aSS S 368 272 96 (8 * 0) (by decide)) (wf1 hs788 0 (by exact (by decide : 0 < 12)) : sf788.mem.read64 _ = c29 ∧ _) rfl (wf1 hs788 1 (by exact (by decide : 1 < 12)) : sf788.mem.read64 _ = c30 ∧ _) ?_
  refine x_addsp hrun788 (c15_816 hP hCL 15 kf788) (pc4 _ 816 820 rfl) (aSk S 368 0 _ (by decide)) ?_
  refine x_ret hrun788 (c15_820 hP hCL 15 kf788) rfl ?_
  exact hcont _ _ _ _ _ hrun788 kf788 hvs788 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Satisfies.of_eq hs788 (by ac_rfl))

end X25519Dalek.LP

end
end

section
section
/-! # Block 15: the ladder loop

`LInv … j`: from the loop head (offset 192) with `j` bits left, the two points in the frame equal the
ladder's state up to the pending swap `sv`, the run reaches `Q`. Proved for all `j ≤ 254` by induction:
`j = 0` is the exit (`b15_exit`), `j + 1` is one iterator step (`b15_head`) and one ladder step
(`b15_mid`) followed by `LInv j`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj

def LInv (mpl : MultiPlacement) (m0 : Memory) (S out sc : BitVec 64) (F : SepProp) (Q : State → Prop)
    (vo : BitVec 5 → BitVec 128) (sbs : List (BitVec 8)) (u0 u1 u2 u3 u4 : BitVec 64) (j : Nat) : Prop :=
  ∀ (sb : State) (r : BitVec 5 → BitVec 64) (ps : PState) (m : Memory) (v : BitVec 5 → BitVec 128)
    (X0 X1 : List (BitVec 64)) (bb : BitVec 8) (sv : Nat) (x0 x1 : MontProjPoint),
    sb.status = .Running → m0.KeepsFrozen m → VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨vo⟩ →
    r 19#5 = out → r 21#5 = 0#64 → r 29#5 = S - 96#64 → r 0#5 = BitVec.ofNat 64 sv → sv < 2 →
    X0.length = 10 → X1.length = 10 →
    montProjBounded (X0.flatMap unpack64) (2 ^ 52) → montProjBounded (X1.flatMap unpack64) (2 ^ 52) →
    montLadderLoop 255 (leBytesToNat sbs) (fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519)
        ⟨1, 0⟩ ⟨fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519, 1⟩ =
      montLadderLoop j (leBytesToNat sbs) (fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519) x0 x1 →
    (montProjOfBytes (X0.flatMap unpack64), montProjOfBytes (X1.flatMap unpack64)) =
      (if sv = 1 then (x1, x0) else (x0, x1)) →
    (m ⊨ ((S - 360#64) ↦₆₄* [u0, u1, u2, u3, u4]) ∗ ((S - 320#64) ↦₆₄* X0) ∗ ((S - 240#64) ↦₆₄* X1) ∗
      ((S - 148#64) ↦ₛ [bb]) ∗ ((S - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 j]) ∗
      memRegion ((S - 368#64) - 1312#64) 1312 ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ (sc ↦ₛ sbs) ∗ F) →
    Reach (bprog mpl 15) (mkS sb (mpl.base 15 + BitVec.ofNat 64 192) r (S - 368#64) ps m v) Q

theorem swap_sel {α : Type} (PA PB x0 x1 : α) (bit sv : Nat) (hb : bit < 2) (hs : sv < 2)
    (h : (PA, PB) = if sv = 1 then (x1, x0) else (x0, x1)) :
    (if bit = sv then PA else PB) = (if bit = 1 then x1 else x0) ∧
      (if bit = sv then PB else PA) = (if bit = 1 then x0 else x1) := by
  rcases (show bit = 0 ∨ bit = 1 by omega) with rfl | rfl <;>
    rcases (show sv = 0 ∨ sv = 1 by omega) with rfl | rfl <;> simp_all

theorem proj_ite (c : Prop) [Decidable c] (A B : List (BitVec 64)) :
    montProjOfBytes ((if c then A else B).flatMap unpack64) =
      if c then montProjOfBytes (A.flatMap unpack64) else montProjOfBytes (B.flatMap unpack64) := by
  split <;> rfl

theorem b52_53 {bs : List (BitVec 8)} (h : montProjBounded bs (2 ^ 52)) : montProjBounded bs (2 ^ 53) :=
  montb_mono h (Nat.pow_le_pow_right (by decide) (by decide))

theorem b15_iter {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {S out sc : BitVec 64} {F : SepProp} {Q : State → Prop}
    {vo : BitVec 5 → BitVec 128} {sbs : List (BitVec 8)} (hal : (S &&& 15#64 == 0#64) = true)
    {u0 u1 u2 u3 u4 : BitVec 64} (hUb : fe51LimbsBounded ([u0, u1, u2, u3, u4].flatMap unpack64) (2 ^ 54))
    {j : Nat} (hL : LInv mpl m0 S out sc F Q vo sbs u0 u1 u2 u3 u4 j)
    {sb : State} {r : BitVec 5 → BitVec 64} {ps : PState} {m : Memory} {v : BitVec 5 → BitVec 128}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 64} {bb : BitVec 8} {sv : Nat}
    {x0 x1 : MontProjPoint}
    (hrun : sb.status = .Running) (kf : m0.KeepsFrozen m)
    (hvs : VRegFile.calleeSaved ⟨v⟩ = VRegFile.calleeSaved ⟨vo⟩)
    (hr19 : r 19#5 = out) (hr20 : r 20#5 = 0#64) (hr21 : r 21#5 = 0#64)
    (hr22 : r 22#5 = BitVec.ofNat 64 (leBytesToNat sbs / 2 ^ j % 2))
    (hr29 : r 29#5 = S - 96#64) (hr0 : r 0#5 = BitVec.ofNat 64 sv) (hsv : sv < 2)
    (hA : montProjBounded ([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].flatMap unpack64) (2 ^ 52))
    (hB : montProjBounded ([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9].flatMap unpack64) (2 ^ 52))
    (hspec : montLadderLoop 255 (leBytesToNat sbs) (fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519)
        ⟨1, 0⟩ ⟨fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519, 1⟩ =
      montLadderLoop (j + 1) (leBytesToNat sbs) (fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519) x0 x1)
    (hrel : (montProjOfBytes ([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9].flatMap unpack64),
        montProjOfBytes ([b0, b1, b2, b3, b4, b5, b6, b7, b8, b9].flatMap unpack64)) =
      (if sv = 1 then (x1, x0) else (x0, x1)))
    (hs : m ⊨ ((S - 360#64) ↦₆₄* [u0, u1, u2, u3, u4]) ∗ ((S - 320#64) ↦₆₄* [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]) ∗
      ((S - 240#64) ↦₆₄* [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗
      ((S - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 j]) ∗ memRegion ((S - 368#64) - 1312#64) 1312 ∗
      (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ (sc ↦ₛ sbs) ∗ F) :
    Reach (bprog mpl 15) (mkS sb (mpl.base 15 + BitVec.ofNat 64 248) r (S - 368#64) ps m v) Q := by
  have hbit : leBytesToNat sbs / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by decide)
  refine b15_mid (F := ((S - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 j]) ∗ (sc ↦ₛ sbs) ∗ F) hP hCL hal hrun kf hvs
    hr19 hr20 hr21 hr22 hr29 hr0 hbit hsv (b52_53 hA) (b52_53 hB) hUb (Satisfies.of_eq hs (by ac_rfl)) ?_
  intro sb' r' ps' m' v' R0 R1 h1 h2 h3 h4 h5 h6 h7 hl0 hl1 hb0 hb1 hv0 hv1 hs'
  obtain ⟨hp0, hp1⟩ := swap_sel _ _ x0 x1 _ sv hbit hsv hrel
  rw [proj_ite, hp0, proj_ite, hp1] at hv0 hv1
  refine hL sb' r' ps' m' v' R0 R1 _ (leBytesToNat sbs / 2 ^ j % 2)
    (if leBytesToNat sbs / 2 ^ j % 2 = 1 then (montDiffAddAndDouble (fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519)
      (if leBytesToNat sbs / 2 ^ j % 2 = 1 then x1 else x0) (if leBytesToNat sbs / 2 ^ j % 2 = 1 then x0 else x1)).2
      else (montDiffAddAndDouble (fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519)
      (if leBytesToNat sbs / 2 ^ j % 2 = 1 then x1 else x0) (if leBytesToNat sbs / 2 ^ j % 2 = 1 then x0 else x1)).1)
    (if leBytesToNat sbs / 2 ^ j % 2 = 1 then (montDiffAddAndDouble (fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519)
      (if leBytesToNat sbs / 2 ^ j % 2 = 1 then x1 else x0) (if leBytesToNat sbs / 2 ^ j % 2 = 1 then x0 else x1)).1
      else (montDiffAddAndDouble (fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519)
      (if leBytesToNat sbs / 2 ^ j % 2 = 1 then x1 else x0) (if leBytesToNat sbs / 2 ^ j % 2 = 1 then x0 else x1)).2)
    h1 h2 h3 h4 h5 h6 h7 hbit hl0 hl1 hb0 hb1 ?_ ?_ (Satisfies.of_eq hs' (by ac_rfl))
  · rw [hspec]
    exact montLadderLoop_step_eq j _ _ x0 x1 _ rfl _ _ _ _
      (by split <;> rfl) rfl rfl
  · rw [hv0, hv1]
    rcases (show leBytesToNat sbs / 2 ^ j % 2 = 0 ∨ leBytesToNat sbs / 2 ^ j % 2 = 1 by omega) with h | h <;>
      simp [h]

theorem b15_step {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {S out sc : BitVec 64} {F : SepProp} {Q : State → Prop}
    {vo : BitVec 5 → BitVec 128} {sbs : List (BitVec 8)} (hsl : sbs.length = 32) (hal : (S &&& 15#64 == 0#64) = true)
    {u0 u1 u2 u3 u4 : BitVec 64} (hUb : fe51LimbsBounded ([u0, u1, u2, u3, u4].flatMap unpack64) (2 ^ 54))
    (j : Nat) (hj : j < 254) (hL : LInv mpl m0 S out sc F Q vo sbs u0 u1 u2 u3 u4 j) :
    LInv mpl m0 S out sc F Q vo sbs u0 u1 u2 u3 u4 (j + 1) := by
  intro sb r ps m v X0 X1 bb sv x0 x1 hrun kf hvs hr19 hr21 hr29 hr0 hsv hl0 hl1 hb0 hb1 hspec hrel hs
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, rfl⟩ := pw_list10 X0 hl0
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, rfl⟩ := pw_list10 X1 hl1
  refine b15_head (F := ((S - 360#64) ↦₆₄* [u0, u1, u2, u3, u4]) ∗
      ((S - 320#64) ↦₆₄* [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]) ∗
      ((S - 240#64) ↦₆₄* [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]) ∗ ((S - 148#64) ↦ₛ [bb]) ∗
      memRegion ((S - 368#64) - 1312#64) 1312 ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ F)
    hP hCL hsl hal hj hrun kf hvs hr19 hr21 hr29 hr0 (Satisfies.of_eq hs (by ac_rfl)) ?_
  intro sb' r' ps' m' v' h1 h2 h3 h4 h5 h6 h7 h8 h9 hs'
  exact b15_iter hP hCL hal hUb hL h1 h2 h3 h4 h5 h6 h7 h8 h9 hsv hb0 hb1 hspec hrel
    (Satisfies.of_eq hs' (by ac_rfl))

end X25519Dalek.LP

end
end

section
section
/-! # `<&MontgomeryPoint as Mul<&Scalar>>::mul` (block 15) meets `montgomeryPointMulSpec`

The frame is split into the pieces the code uses, `b15_entry` runs the prologue, the decoding of `u`
and the first bit (`Rev::nth`), `b15_iter` the first ladder step, `b15_loop` the remaining 254
steps (by induction, `b15_step`), and `b15_zero` the final select, `as_affine` and the epilogue;
the frame is then merged back into one region. After DeepMind's `Shared51/MontgomeryLadderCode.lean`
(google-deepmind/code-verification @ 8c8d371f, `montgomery_point_mul_ok_of`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace X25519Dalek.LP

open Arm64 hiding fpAdd fpSub fpMul fpNeg
open Arm64.Obj

theorem b15_zero {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {S out sc : BitVec 64} {Fr : SepProp} {Q : State → Prop}
    {vo : BitVec 5 → BitVec 128} {sbs : List (BitVec 8)} (hal : (S &&& 15#64 == 0#64) = true)
    {u0 u1 u2 u3 u4 : BitVec 64} {c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 : BitVec 64}
    {ob : List (BitVec 8)} (hol : ob.length = 32)
    (hfin : ∀ (sb' : State) (r' : BitVec 5 → BitVec 64) (ps' : PState) (m' : Memory) (v' : BitVec 5 → BitVec 128)
      (XS X1' : List (BitVec 64)), XS.length = 10 → X1'.length = 10 →
      sb'.status = .Running → m0.KeepsFrozen m' → VRegFile.calleeSaved ⟨v'⟩ = VRegFile.calleeSaved ⟨vo⟩ →
      r' 19#5 = c19 → r' 20#5 = c20 → r' 21#5 = c21 → r' 22#5 = c22 → r' 23#5 = c23 → r' 24#5 = c24 →
      r' 25#5 = c25 → r' 26#5 = c26 → r' 27#5 = c27 → r' 28#5 = c28 → r' 29#5 = c29 →
      (m' ⊨ ((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗
        ((S - 320#64) ↦₆₄* XS) ∗
        (out ↦ₛ natToLeBytes 32
          (fpMul (montLadderLoop 255 (leBytesToNat sbs) (fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519)
              ⟨1, 0⟩ ⟨fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519, 1⟩).U
            (fpInv (montLadderLoop 255 (leBytesToNat sbs) (fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519)
              ⟨1, 0⟩ ⟨fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519, 1⟩).W))) ∗
        memRegion ((S - 368#64) - 1312#64) 1312 ∗ ((S - 148#64) ↦ₛ [0#8]) ∗ ((S - 240#64) ↦₆₄* X1') ∗
        ((S - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 0]) ∗ ((S - 360#64) ↦₆₄* [u0, u1, u2, u3, u4]) ∗
        (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ (sc ↦ₛ sbs) ∗ Fr) →
      Reach (bprog mpl 15) (mkS sb' c30 r' (S - 0#64) ps' m' v') Q) :
    LInv mpl m0 S out sc (((S - 96#64) ↦₆₄* [c29, c30, c28, c27, c26, c25, c24, c23, c22, c21, c20, c19]) ∗
      (out ↦ₛ ob) ∗ Fr) Q vo sbs u0 u1 u2 u3 u4 0 := by
  intro sb r ps m v X0 X1 bb sv x0 x1 hrun kf hvs hr19 hr21 hr29 hr0 hsv hl0 hl1 hb0 hb1 hspec hrel hs
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, rfl⟩ := pw_list10 X0 hl0
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, rfl⟩ := pw_list10 X1 hl1
  refine b15_exit (F := ((S - 360#64) ↦₆₄* [u0, u1, u2, u3, u4]) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗
      (sc ↦ₛ sbs) ∗ Fr) hP hCL hal hol hsv hrun kf hvs hr19 hr21 hr29 hr0 hb0 hb1
    (Satisfies.of_eq hs (by ac_rfl)) ?_
  intro sb' r' ps' m' v' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hs'
  have hsel : montProjOfBytes ((if sv = 1 then [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]
      else [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]).flatMap unpack64) =
      montLadderLoop 255 (leBytesToNat sbs) (fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519)
        ⟨1, 0⟩ ⟨fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519, 1⟩ := by
    rw [hspec, proj_ite]
    simp only [montLadderLoop]
    rcases (show sv = 0 ∨ sv = 1 by omega) with rfl | rfl <;> simp_all
  rw [hsel] at hs'
  exact hfin sb' r' ps' m' v' (if sv = 1 then [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9]
      else [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]) [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] (by split <;> rfl) rfl h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    (Satisfies.of_eq hs' (by ac_rfl))

theorem b15_loop {mpl : MultiPlacement} (hP : x25519CliMultiLib.Placeable mpl) {m0 : Memory}
    (hCL : x25519CliMultiLib.CodeLoaded mpl m0) {S out sc : BitVec 64} {F : SepProp} {Q : State → Prop}
    {vo : BitVec 5 → BitVec 128} {sbs : List (BitVec 8)} (hsl : sbs.length = 32) (hal : (S &&& 15#64 == 0#64) = true)
    {u0 u1 u2 u3 u4 : BitVec 64} (hUb : fe51LimbsBounded ([u0, u1, u2, u3, u4].flatMap unpack64) (2 ^ 54))
    (h0 : LInv mpl m0 S out sc F Q vo sbs u0 u1 u2 u3 u4 0) :
    ∀ j, j ≤ 254 → LInv mpl m0 S out sc F Q vo sbs u0 u1 u2 u3 u4 j := by
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ j ih => intro hj; exact b15_step hP hCL hsl hal hUb j (by omega) (ih (by omega))

theorem b_list12 {α : Type} (l : List α) (h : l.length = 12) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11, l = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] := by
  match l, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11], _ =>
    exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, rfl⟩

theorem b_list1 {α : Type} (l : List α) (h : l.length = 1) : ∃ a0, l = [a0] := by
  match l, h with
  | [a0], _ => exact ⟨a0, rfl⟩

theorem sat_mr_words' {m : Memory} {a b : BitVec 64} {ws : List (BitVec 64)} {F : SepProp} (n k : Nat)
    (hn : n < 2 ^ 64) (hb : b = a + BitVec.ofNat 64 n) (hl : ws.length = k)
    (hs : m ⊨ memRegion a n ∗ (b ↦₆₄* ws) ∗ F) : m ⊨ memRegion a (n + 8 * k) ∗ F := by
  rw [words_eq_bytes] at hs
  have h := sat_mr_bytes n hn hb hs
  rwa [flatMap_unpack64_length, hl] at h

theorem aF (S : BitVec 64) (n c : Nat) (h : BitVec.ofNat 64 1680 - BitVec.ofNat 64 n = BitVec.ofNat 64 c) :
    S - BitVec.ofNat 64 c = S - BitVec.ofNat 64 1680 + BitVec.ofNat 64 n :=
  (aSb S 1680 n c h).symm

abbrev mpmName : String :=
  "<&curve25519_dalek::montgomery::MontgomeryPoint as core::ops::arith::Mul<&curve25519_dalek::scalar::Scalar>>::mul"

theorem lk15 : lookupBlockSym mpmName x25519CliMultiLib.blocks = some (15, 0) := by decide +kernel

theorem one_val : fe51Val 1#64 0#64 0#64 0#64 0#64 % p25519 = 1 := by decide
theorem zero_val : fe51Val 0#64 0#64 0#64 0#64 0#64 % p25519 = 0 := by decide

set_option maxHeartbeats 8000000 in
theorem mpm_ok : fnOk mpmName montgomeryPointMulSpec := by
  refine ⟨15, 0, lk15, fun mpl hP => ?_⟩
  intro x R s0 hpc hrun hpre hal hCLp
  obtain ⟨out, self, sc, ob, selfb, sbs⟩ := x
  have hfa : x25519CliMultiLib.fnAddr mpl mpmName = mpl.base 15 := by
    simp [MultiPlacedLib.fnAddr, lk15]
  rw [hfa] at hpc
  simp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec] at hpre
  have h1 := Satisfies.of_eq hpre
    (Q := ⌜s0.readReg64 Reg.x8 = out ∧ s0.readReg64 Reg.x0 = self ∧ s0.readReg64 Reg.x1 = sc ∧
        ob.length = 32 ∧ selfb.length = 32 ∧ sbs.length = 32⌝ ∗
      ⌜x25519CliMultiLib.CodeLoaded mpl s0.mem⌝ ∗ stackFrame s0 1680 ∗ (self ↦ₛ selfb) ∗ (sc ↦ₛ sbs) ∗
      (fe51_one mpl ↦ᵣ fe51OneBytes) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ (out ↦ₛ ob) ∗ R) (by ac_rfl)
  rw [sat_pure_sep, sat_pure_sep] at h1
  obtain ⟨⟨hx8, hx0, hx1, hol, hsell, hsl⟩, hCL, hs0⟩ := h1
  simp only [stackFrame] at hs0
  have hal' : (s0.sp &&& 15#64 == 0#64) = true := hal
  have hr0 : s0.regs.regs 0#5 = self := by rw [← readGpr_eq s0 0#5 (by decide)]; exact hx0
  have hr1 : s0.regs.regs 1#5 = sc := by rw [← readGpr_eq s0 1#5 (by decide)]; exact hx1
  have hr8 : s0.regs.regs 8#5 = out := by rw [← readGpr_eq s0 8#5 (by decide)]; exact hx8
  -- the frame, piece by piece
  replace hs0 := sat_mr_split (a := s0.sp - BitVec.ofNat 64 1680) 1312 368 (by decide) (s0.sp - 368#64) (aSb _ 1680 1312 368 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 368#64) 8 360 (by decide) (s0.sp - 360#64) (aSb _ 368 8 360 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 360#64) 40 320 (by decide) (s0.sp - 320#64) (aSb _ 360 40 320 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 320#64) 80 240 (by decide) (s0.sp - 240#64) (aSb _ 320 80 240 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 240#64) 80 160 (by decide) (s0.sp - 160#64) (aSb _ 240 80 160 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 160#64) 12 148 (by decide) (s0.sp - 148#64) (aSb _ 160 12 148 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 148#64) 1 147 (by decide) (s0.sp - 147#64) (aSb _ 148 1 147 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 147#64) 3 144 (by decide) (s0.sp - 144#64) (aSb _ 147 3 144 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 144#64) 24 120 (by decide) (s0.sp - 120#64) (aSb _ 144 24 120 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 120#64) 8 112 (by decide) (s0.sp - 112#64) (aSb _ 120 8 112 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  replace hs0 := sat_mr_split (a := s0.sp - 112#64) 16 96 (by decide) (s0.sp - 96#64) (aSb _ 112 16 96 (by decide)) hs0
  rw [sepConj_left_comm] at hs0
  -- hs0 : SV96 ∗ s16 ∗ SP8 ∗ IT ∗ s3 ∗ B ∗ s12 ∗ X1 ∗ X0 ∗ U ∗ s8 ∗ C ∗ rest
  obtain ⟨LSV, hLSV, hs0⟩ := memRegion_words' (s0.sp - 96#64) 12 (by decide) hs0
  obtain ⟨sv0, sv1, sv2, sv3, sv4, sv5, sv6, sv7, sv8, sv9, sv10, sv11, rfl⟩ := b_list12 LSV hLSV
  rw [pick3] at hs0
  obtain ⟨LSP, hLSP, hs0⟩ := memRegion_words' (s0.sp - 120#64) 1 (by decide) hs0
  obtain ⟨g0, rfl⟩ := b_list1 LSP hLSP
  rw [pick4] at hs0
  obtain ⟨LIT, hLIT, hs0⟩ := memRegion_words' (s0.sp - 144#64) 3 (by decide) hs0
  obtain ⟨it0, it1, it2, hIT⟩ : ∃ a b c, LIT = [a, b, c] := by
    match LIT, hLIT with
    | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
  subst hIT
  rw [pick6] at hs0
  obtain ⟨LB, hLB, hs0⟩ := memRegion_bytes (s0.sp - 148#64) 1 (by decide) hs0
  obtain ⟨bb0, rfl⟩ := b_list1 LB hLB
  rw [pick8] at hs0
  obtain ⟨LX1, hLX1, hs0⟩ := memRegion_words' (s0.sp - 240#64) 10 (by decide) hs0
  obtain ⟨xb0, xb1, xb2, xb3, xb4, xb5, xb6, xb7, xb8, xb9, rfl⟩ := pw_list10 LX1 hLX1
  rw [pick9] at hs0
  obtain ⟨LX0, hLX0, hs0⟩ := memRegion_words' (s0.sp - 320#64) 10 (by decide) hs0
  obtain ⟨xa0, xa1, xa2, xa3, xa4, xa5, xa6, xa7, xa8, xa9, rfl⟩ := pw_list10 LX0 hLX0
  rw [pick10] at hs0
  obtain ⟨LU, hLU, hs0⟩ := memRegion_words' (s0.sp - 360#64) 5 (by decide) hs0
  obtain ⟨uw0, uw1, uw2, uw3, uw4, rfl⟩ := list5 LU hLU
  rw [show s0.sp - BitVec.ofNat 64 1680 = (s0.sp - 368#64) - 1312#64 from (addr_sub_sub _ 368 1312).symm] at hs0
  -- the run
  have e0 : mkS s0 (mpl.base 15) s0.regs.regs (s0.sp - 0#64) s0.pstate s0.mem s0.vregs.regs = s0 := by
    rw [BitVec.sub_zero, ← hpc]; rfl
  show Reach _ s0 _
  conv => enter [2]; rw [← e0]
  generalize hQ : SubroutineOutcome _ _ _ _ = Q
  refine b15_entry (F := ((s0.sp - 148#64) ↦ₛ [bb0]) ∗ (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ (out ↦ₛ ob) ∗
      memRegion (s0.sp - 368#64) 8 ∗ memRegion (s0.sp - 160#64) 12 ∗ memRegion (s0.sp - 147#64) 3 ∗
      memRegion (s0.sp - 112#64) 16 ∗ R) (vo := s0.vregs.regs)
    hP hCL hsl hsell hal' hrun (Memory.KeepsFrozen.refl _) rfl hr0 hr1 hr8 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl (Satisfies.of_eq hs0 (by ac_rfl)) ?_
  intro sb' r' ps' m' v' u0 u1 u2 u3 u4 h1 h2 h3 h4 h5 h6 h7 h8 h9 hu hs'
  obtain ⟨hu0, hu1, hu2, hu3, hu4, hval⟩ := hu
  have l51 : ∀ x : BitVec 64, x.toNat < 2 ^ 51 → ∀ k, 51 ≤ k → x.toNat < 2 ^ k :=
    fun x hx k hk => Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hk)
  have hUb : fe51LimbsBounded ([u0, u1, u2, u3, u4].flatMap unpack64) (2 ^ 54) :=
    (lbw _ _ _ _ _ _).mpr ⟨l51 _ hu0 54 (by decide), l51 _ hu1 54 (by decide), l51 _ hu2 54 (by decide),
      l51 _ hu3 54 (by decide), l51 _ hu4 54 (by decide)⟩
  have hvu : fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) = decodeU255 selfb := by rw [valw, hval]
  have hfin : ∀ (sb' : State) (r' : BitVec 5 → BitVec 64) (ps' : PState) (m' : Memory) (v' : BitVec 5 → BitVec 128)
      (XS X1' : List (BitVec 64)), XS.length = 10 → X1'.length = 10 →
      sb'.status = .Running → s0.mem.KeepsFrozen m' →
      VRegFile.calleeSaved ⟨v'⟩ = VRegFile.calleeSaved ⟨s0.vregs.regs⟩ →
      r' 19#5 = s0.regs.regs 19#5 → r' 20#5 = s0.regs.regs 20#5 → r' 21#5 = s0.regs.regs 21#5 →
      r' 22#5 = s0.regs.regs 22#5 → r' 23#5 = s0.regs.regs 23#5 → r' 24#5 = s0.regs.regs 24#5 →
      r' 25#5 = s0.regs.regs 25#5 → r' 26#5 = s0.regs.regs 26#5 → r' 27#5 = s0.regs.regs 27#5 →
      r' 28#5 = s0.regs.regs 28#5 → r' 29#5 = s0.regs.regs 29#5 →
      (m' ⊨ ((s0.sp - 96#64) ↦₆₄* [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 28#5, s0.regs.regs 27#5,
          s0.regs.regs 26#5, s0.regs.regs 25#5, s0.regs.regs 24#5, s0.regs.regs 23#5, s0.regs.regs 22#5,
          s0.regs.regs 21#5, s0.regs.regs 20#5, s0.regs.regs 19#5]) ∗
        ((s0.sp - 320#64) ↦₆₄* XS) ∗
        (out ↦ₛ natToLeBytes 32
          (fpMul (montLadderLoop 255 (leBytesToNat sbs) (fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519)
              ⟨1, 0⟩ ⟨fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519, 1⟩).U
            (fpInv (montLadderLoop 255 (leBytesToNat sbs) (fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519)
              ⟨1, 0⟩ ⟨fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519, 1⟩).W))) ∗
        memRegion ((s0.sp - 368#64) - 1312#64) 1312 ∗ ((s0.sp - 148#64) ↦ₛ [0#8]) ∗ ((s0.sp - 240#64) ↦₆₄* X1') ∗
        ((s0.sp - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 0]) ∗ ((s0.sp - 360#64) ↦₆₄* [u0, u1, u2, u3, u4]) ∗
        (fe51_mont_a24 mpl ↦ᵣ fe51MontA24Bytes) ∗ (sc ↦ₛ sbs) ∗
        (((s0.sp - 120#64) ↦₆₄* [0#64]) ∗ (self ↦ₛ selfb) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
          memRegion (s0.sp - 368#64) 8 ∗ memRegion (s0.sp - 160#64) 12 ∗ memRegion (s0.sp - 147#64) 3 ∗
          memRegion (s0.sp - 112#64) 16 ∗ R)) →
      Reach (bprog mpl 15) (mkS sb' (s0.regs.regs 30#5) r' (s0.sp - 0#64) ps' m' v') Q := by
    intro sb2 r2 ps2 m2 v2 XS X1' hXS hX1' g1 g2 g3 k19 k20 k21 k22 k23 k24 k25 k26 k27 k28 k29 hm
    apply Reach.done
    rw [← hQ]
    left
    refine ⟨⟨(readGpr_eq s0 30#5 (by decide)).symm, BitVec.sub_zero _, g1⟩, ⟨BitVec.sub_zero _, ?_⟩, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, g3⟩
      · rw [mkS_readGpr, readGpr_eq s0 _ (by decide)]; exact k19
      · rw [mkS_readGpr, readGpr_eq s0 _ (by decide)]; exact k20
      · rw [mkS_readGpr, readGpr_eq s0 _ (by decide)]; exact k21
      · rw [mkS_readGpr, readGpr_eq s0 _ (by decide)]; exact k22
      · rw [mkS_readGpr, readGpr_eq s0 _ (by decide)]; exact k23
      · rw [mkS_readGpr, readGpr_eq s0 _ (by decide)]; exact k24
      · rw [mkS_readGpr, readGpr_eq s0 _ (by decide)]; exact k25
      · rw [mkS_readGpr, readGpr_eq s0 _ (by decide)]; exact k26
      · rw [mkS_readGpr, readGpr_eq s0 _ (by decide)]; exact k27
      · rw [mkS_readGpr, readGpr_eq s0 _ (by decide)]; exact k28
      · show (mkS sb2 (s0.regs.regs 30#5) r2 (s0.sp - 0#64) ps2 m2 v2).readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5)
        rw [mkS_readGpr, readGpr_eq s0 _ (by decide)]; exact k29
    simp only [ToBaseSpec.toSpec, stackFrame, mkS_sp, mkS_mem, BitVec.sub_zero, MultiPlacedLib.withCodeLoaded]
    rw [hvu] at hm
    rw [show (s0.sp - 368#64) - 1312#64 = s0.sp - BitVec.ofNat 64 1680 from addr_sub_sub _ 368 1312] at hm
    simp only [sepConj_left_comm _ (memRegion (s0.sp - 368#64) 8)] at hm
    simp only [sepConj_left_comm _ (memRegion (s0.sp - BitVec.ofNat 64 1680) 1312)] at hm
    replace hm := sat_mr_merge 1312 8 (by decide) (aF _ _ 368 (by decide)) hm
    simp only [sepConj_left_comm _ ((s0.sp - 360#64) ↦₆₄* [u0, u1, u2, u3, u4])] at hm
    simp only [sepConj_left_comm _ (memRegion (s0.sp - BitVec.ofNat 64 1680) _)] at hm
    replace hm := sat_mr_words' _ 5 (by decide) (aF _ _ 360 (by decide)) rfl hm
    simp only [sepConj_left_comm _ ((s0.sp - 320#64) ↦₆₄* XS)] at hm
    simp only [sepConj_left_comm _ (memRegion (s0.sp - BitVec.ofNat 64 1680) _)] at hm
    replace hm := sat_mr_words' _ 10 (by decide) (aF _ _ 320 (by decide)) hXS hm
    simp only [sepConj_left_comm _ ((s0.sp - 240#64) ↦₆₄* X1')] at hm
    simp only [sepConj_left_comm _ (memRegion (s0.sp - BitVec.ofNat 64 1680) _)] at hm
    replace hm := sat_mr_words' _ 10 (by decide) (aF _ _ 240 (by decide)) hX1' hm
    simp only [sepConj_left_comm _ (memRegion (s0.sp - 160#64) 12)] at hm
    simp only [sepConj_left_comm _ (memRegion (s0.sp - BitVec.ofNat 64 1680) _)] at hm
    replace hm := sat_mr_merge _ 12 (by decide) (aF _ _ 160 (by decide)) hm
    simp only [sepConj_left_comm _ ((s0.sp - 148#64) ↦ₛ [0#8])] at hm
    simp only [sepConj_left_comm _ (memRegion (s0.sp - BitVec.ofNat 64 1680) _)] at hm
    replace hm := sat_mr_bytes _ (by decide) (aF _ _ 148 (by decide)) hm
    simp only [sepConj_left_comm _ (memRegion (s0.sp - 147#64) 3)] at hm
    simp only [sepConj_left_comm _ (memRegion (s0.sp - BitVec.ofNat 64 1680) _)] at hm
    replace hm := sat_mr_merge _ 3 (by decide) (aF _ _ 147 (by decide)) hm
    simp only [sepConj_left_comm _ ((s0.sp - 144#64) ↦₆₄* [sc, 0#64, BitVec.ofNat 64 0])] at hm
    simp only [sepConj_left_comm _ (memRegion (s0.sp - BitVec.ofNat 64 1680) _)] at hm
    replace hm := sat_mr_words' _ 3 (by decide) (aF _ _ 144 (by decide)) rfl hm
    simp only [sepConj_left_comm _ ((s0.sp - 120#64) ↦₆₄* [0#64])] at hm
    simp only [sepConj_left_comm _ (memRegion (s0.sp - BitVec.ofNat 64 1680) _)] at hm
    replace hm := sat_mr_words' _ 1 (by decide) (aF _ _ 120 (by decide)) rfl hm
    simp only [sepConj_left_comm _ (memRegion (s0.sp - 112#64) 16)] at hm
    simp only [sepConj_left_comm _ (memRegion (s0.sp - BitVec.ofNat 64 1680) _)] at hm
    replace hm := sat_mr_merge _ 16 (by decide) (aF _ _ 112 (by decide)) hm
    simp only [sepConj_left_comm _ ((s0.sp - 96#64) ↦₆₄* [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 28#5, s0.regs.regs 27#5, s0.regs.regs 26#5, s0.regs.regs 25#5, s0.regs.regs 24#5, s0.regs.regs 23#5, s0.regs.regs 22#5, s0.regs.regs 21#5, s0.regs.regs 20#5, s0.regs.regs 19#5])] at hm
    simp only [sepConj_left_comm _ (memRegion (s0.sp - BitVec.ofNat 64 1680) _)] at hm
    replace hm := sat_mr_words' _ 12 (by decide) (aF _ _ 96 (by decide)) rfl hm
    simp only [List.length_singleton, Nat.reduceAdd, Nat.reduceMul] at hm
    exact Satisfies.of_eq hm (by ac_rfl)
  have hX0 : montProjBounded ([1#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64].flatMap unpack64) (2 ^ 52) :=
    pw_montb_of_words _ _ _ _ _ _ _ _ _ _ _ ((lbw _ _ _ _ _ _).mpr (by decide)) ((lbw _ _ _ _ _ _).mpr (by decide))
  have hX1 : montProjBounded ([u0, u1, u2, u3, u4, 1#64, 0#64, 0#64, 0#64, 0#64].flatMap unpack64) (2 ^ 52) :=
    pw_montb_of_words _ _ _ _ _ _ _ _ _ _ _ ((lbw _ _ _ _ _ _).mpr ⟨l51 _ hu0 52 (by decide), l51 _ hu1 52 (by decide),
      l51 _ hu2 52 (by decide), l51 _ hu3 52 (by decide), l51 _ hu4 52 (by decide)⟩) ((lbw _ _ _ _ _ _).mpr (by decide))
  refine b15_iter (F := ((s0.sp - 96#64) ↦₆₄* [s0.regs.regs 29#5, s0.regs.regs 30#5, s0.regs.regs 28#5,
      s0.regs.regs 27#5, s0.regs.regs 26#5, s0.regs.regs 25#5, s0.regs.regs 24#5, s0.regs.regs 23#5,
      s0.regs.regs 22#5, s0.regs.regs 21#5, s0.regs.regs 20#5, s0.regs.regs 19#5]) ∗ (out ↦ₛ ob) ∗
      (((s0.sp - 120#64) ↦₆₄* [0#64]) ∗ (self ↦ₛ selfb) ∗ (fe51_one mpl ↦ᵣ fe51OneBytes) ∗
        memRegion (s0.sp - 368#64) 8 ∗ memRegion (s0.sp - 160#64) 12 ∗ memRegion (s0.sp - 147#64) 3 ∗
        memRegion (s0.sp - 112#64) 16 ∗ R))
    (j := 254) (x0 := ⟨1, 0⟩) (x1 := ⟨fe51ValOfBytes ([u0, u1, u2, u3, u4].flatMap unpack64) % p25519, 1⟩)
    hP hCL hal' hUb (b15_loop hP hCL hsl hal' hUb (b15_zero hP hCL hal' hol hfin) 254 (le_refl _))
    h1 h2 h3 h4 h5 h6 h7 h8 h9 (by decide) hX0 hX1 rfl ?_ (Satisfies.of_eq hs' (by ac_rfl))
  simp only [pw_montProj_words, valw, one_val, zero_val]
  simp

end X25519Dalek.LP

namespace X25519Dalek

theorem fnOk_montgomeryPoint_mul_v2_dev :
    fnOk
      "<&curve25519_dalek::montgomery::MontgomeryPoint as core::ops::arith::Mul<&curve25519_dalek::scalar::Scalar>>::mul"
      montgomeryPointMulSpec :=
  LP.mpm_ok

end X25519Dalek

end
end

section
open X25519Dalek

theorem solution :
    fnOk
      "<&curve25519_dalek::montgomery::MontgomeryPoint as core::ops::arith::Mul<&curve25519_dalek::scalar::Scalar>>::mul"
      montgomeryPointMulSpec := by
  apply X25519Dalek.fnOk_montgomeryPoint_mul_v2_dev <;> assumption

end
