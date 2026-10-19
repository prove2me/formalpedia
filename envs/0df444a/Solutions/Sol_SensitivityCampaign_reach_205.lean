-- Prove2me | solution 1 for SensitivityCampaign.reach_205
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-10-16T16:49:20.019547+00:00
-- url     : https://prove2.me/submissions/39b2d7f4-3948-4bc3-b4bb-9875317f6c37

/-
Block sensitivity versus sensitivity: exponent 2.05.
Lean 4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

The campaign definition is imported unchanged. All auxiliary theorem proofs
are included below; there are no theorem-stub imports. Reused accepted
Prove2Me submissions and upstream OpenAI/math sources are attributed at their
original locations. Local modifications to reused sources remove repeated
helper declarations and imports; the first accepted proof is retained.
New construction and proofs are in namespace Sensitivity205.
-/

import Mathlib
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_OAI_Combinatorics_Sensitivity_Construction
import Definitions.Def_OAI_Combinatorics_Sensitivity_FixedCoordinates
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Iterates
import Definitions.Def_OAI_Combinatorics_Sensitivity_LabelingEvents
import Definitions.Def_OAI_Combinatorics_Sensitivity_Or
import Definitions.Def_OAI_Combinatorics_Sensitivity_ProfileArithmetic
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveCandidates
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_Reindex
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCyclic
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tower
import Definitions.Def_OAI_Combinatorics_Sensitivity_TowerProfiles
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
set_option autoImplicit false


-- Source component: Theorems/Thm_SensitivityCampaign_finite_certificate.lean
section Component0
-- Accepted Prove2Me submission 15dea0b2-cc95-4735-a564-6a71bbd8be32
-- Local packaging: deduplicated identical-name helpers; retained their first accepted proof.
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096


-- Reused in full from OpenAI, Basic.lean

namespace OAI

/-! Finite Boolean flips and the exact maximum/witness interfaces for sensitivity. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J K : Type}

theorem flip_singleton_other (x : I → Bool) {i j : I} (h : j ≠ i) :
    flip x {i} j = x j := by
  simp [flip, h]

theorem flip_insert (x : I → Bool) (i : I) (B : Finset I) (hi : i ∉ B) :
    flip x (insert i B) = flip (flip x B) {i} := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [flip, hi]
  · simp [flip, hji]

theorem flip_prod_same (x : J × I → Bool) (j : J) (i : I) :
    (fun a => flip x {(j, i)} (j, a)) = flip (fun a => x (j, a)) {i} := by
  funext a
  simp [flip]

theorem flip_prod_other (x : J × I → Bool) {j k : J} (i : I) (hk : k ≠ j) :
    (fun a => flip x {(j, i)} (k, a)) = fun a => x (k, a) := by
  funext a
  simp [flip, hk]

section Finite

variable [Fintype I]

theorem flip_differences (x y : I → Bool) :
    flip x (Finset.univ.filter fun i => x i ≠ y i) = y := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [flip, hx, hy]

theorem sensitivityAt_le_card (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ Fintype.card I :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem sensitivityAt_le_sensitivity (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x ≤ sensitivity f :=
  Finset.le_sup (Finset.mem_univ x)

theorem sensitivity_le (f : (I → Bool) → Bool) {n : ℕ}
    (h : ∀ x, sensitivityAt f x ≤ n) : sensitivity f ≤ n :=
  Finset.sup_le fun x _ => h x

theorem sensitivityAt_eq_zero_iff (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivityAt f x = 0 ↔ ∀ i, f (flip x {i}) = f x := by
  simp [sensitivityAt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

theorem sensitivityAt_pos (f : (I → Bool) → Bool) (x : I → Bool) (i : I)
    (hi : f (flip x {i}) ≠ f x) : 0 < sensitivityAt f x :=
  Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

theorem exists_sensitivityAt_eq (f : (I → Bool) → Bool) :
    ∃ x, sensitivityAt f x = sensitivity f := by
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (I → Bool)) (by simp) (sensitivityAt f)
  exact ⟨x, hx.symm⟩

theorem blockSensitivityAt_le_blockSensitivity (f : (I → Bool) → Bool) (x : I → Bool) :
    blockSensitivityAt f x ≤ blockSensitivity f :=
  Finset.le_sup (Finset.mem_univ x)

theorem blockSensitivity_le (f : (I → Bool) → Bool) {n : ℕ}
    (h : ∀ x, blockSensitivityAt f x ≤ n) : blockSensitivity f ≤ n :=
  Finset.sup_le fun x _ => h x

theorem le_blockSensitivityAt (f : (I → Bool) → Bool) (x : I → Bool)
    (blocks : Finset (Finset I))
    (hd : ∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B)
    (hb : ∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) :
    blocks.card ≤ blockSensitivityAt f x := by
  have h := Finset.le_sup (s := (Finset.univ : Finset (Finset (Finset I))))
    (f := fun blocks =>
      if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
          (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
      then blocks.card else 0) (Finset.mem_univ blocks)
  have hv : (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) := ⟨hd, hb⟩
  simpa only [blockSensitivityAt, if_pos hv] using h

theorem blockSensitivityAt_le (f : (I → Bool) → Bool) (x : I → Bool) {n : ℕ}
    (h : ∀ blocks : Finset (Finset I),
      (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) →
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) → blocks.card ≤ n) :
    blockSensitivityAt f x ≤ n := by
  apply Finset.sup_le
  intro blocks _
  split_ifs with hb
  · exact h blocks hb.1 hb.2
  · exact Nat.zero_le _

theorem exists_blockSensitivityAt_family (f : (I → Bool) → Bool) (x : I → Bool) :
    ∃ blocks : Finset (Finset I), blocks.card = blockSensitivityAt f x ∧
      (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x) := by
  obtain ⟨blocks, _, hb⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Finset (Finset I))) (by simp)
    (fun blocks =>
      if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
          (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
      then blocks.card else 0)
  by_cases hv : (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
      (∀ B ∈ blocks, B.Nonempty ∧ f (flip x B) ≠ f x)
  · exact ⟨blocks, by simpa only [blockSensitivityAt, if_pos hv] using hb.symm, hv⟩
  · have hz : blockSensitivityAt f x = 0 := by
      simpa only [blockSensitivityAt, if_neg hv] using hb
    exact ⟨∅, by simp [hz], by simp, by simp⟩

theorem le_blockSensitivityAt_of_family [Fintype K]
    (f : (I → Bool) → Bool) (x : I → Bool) (blocks : K → Finset I)
    (hne : ∀ k, (blocks k).Nonempty)
    (hd : Pairwise fun k l => Disjoint (blocks k) (blocks l))
    (hb : ∀ k, f (flip x (blocks k)) ≠ f x) :
    Fintype.card K ≤ blockSensitivityAt f x := by
  have hinj : Function.Injective blocks := by
    intro k l hkl
    by_contra hnekl
    obtain ⟨i, hi⟩ := hne k
    exact Finset.disjoint_left.mp (hd hnekl) hi (by simpa [← hkl] using hi)
  have hcard := le_blockSensitivityAt f x (Finset.univ.image blocks)
    (by
      intro A hA B hB hAB
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hB
      exact hd (fun h => hAB (congrArg blocks h)))
    (by
      intro B hB
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hB
      exact ⟨hne k, hb k⟩)
  simpa only [sensitivityAt, Finset.card_image_of_injective _ hinj, Finset.card_univ] using hcard

theorem eq_of_singleton_invariant (f : (I → Bool) → Bool)
    (h : ∀ x i, f (flip x {i}) = f x) (x y : I → Bool) : f x = f y := by
  have hflip (B : Finset I) : f (flip x B) = f x := by
    induction B using Finset.induction with
    | empty => simp
    | @insert i B hi ih => rw [flip_insert x i B hi, h, ih]
  rw [← flip_differences x y, hflip]

theorem sensitivity_pos_of_nonconstant (f : (I → Bool) → Bool)
    (h : ∃ x y, f x ≠ f y) : 0 < sensitivity f := by
  by_contra hn
  have hz : sensitivity f = 0 := Nat.eq_zero_of_not_pos hn
  have hi (x : I → Bool) (i : I) : f (flip x {i}) = f x := by
    apply (sensitivityAt_eq_zero_iff f x).mp _ i
    exact Nat.eq_zero_of_le_zero ((sensitivityAt_le_sensitivity f x).trans_eq hz)
  obtain ⟨x, y, hxy⟩ := h
  exact hxy (eq_of_singleton_invariant f hi x y)

end Finite
end Paper320

end

end OAI

-- Reused in full from OpenAI, Composition.lean

namespace OAI

/-! Disjoint Boolean composition, with each child retaining its own raw coordinates. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320

variable {I J : Type}

theorem compose_flip_sensitive_iff (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (x : I × J → Bool) (i : I) (j : J) :
    compose f g (flip x {(i, j)}) ≠ compose f g x ↔
      g (flip (fun a => x (i, a)) {j}) ≠ g (fun a => x (i, a)) ∧
      f (flip (fun k => g (fun a => x (k, a))) {i}) ≠
        f (fun k => g (fun a => x (k, a))) := by
  by_cases hg : g (flip (fun a => x (i, a)) {j}) = g (fun a => x (i, a))
  · have he : (fun k => g (fun a => flip x {(i, j)} (k, a))) =
        fun k => g (fun a => x (k, a)) := by
      funext k
      by_cases hk : k = i
      · subst k
        rw [flip_prod_same, hg]
      · rw [flip_prod_other x j hk]
    simp only [compose, he, ne_eq, not_true_eq_false, hg, false_and]
  · have hn : g (flip (fun a => x (i, a)) {j}) = !(g (fun a => x (i, a))) := by
      cases h₁ : g (flip (fun a => x (i, a)) {j}) <;>
        cases h₂ : g (fun a => x (i, a)) <;> simp_all
    have he : (fun k => g (fun a => flip x {(i, j)} (k, a))) =
        flip (fun k => g (fun a => x (k, a))) {i} := by
      funext k
      by_cases hk : k = i
      · subst k
        rw [flip_prod_same, flip_singleton_self, hn]
      · rw [flip_prod_other x j hk, flip_singleton_other _ hk]
    simp only [compose, he, ne_eq, hg, not_false_eq_true, true_and]

theorem compose_zero (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (hg : g (fun _ => false) = false) :
    compose f g (fun _ => false) = f (fun _ => false) := by
  simp [compose, hg]

theorem compose_flip_product_zero (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (C : Finset I) (D : Finset J) (hg : g (fun _ => false) = false)
    (hD : g (flip (fun _ => false) D) ≠ g (fun _ => false)) :
    compose f g (flip (fun _ => false) (C ×ˢ D)) = f (flip (fun _ => false) C) := by
  have hD' : g (flip (fun _ => false) D) = true := by
    cases he : g (flip (fun _ => false) D) <;> simp_all
  apply congrArg f
  funext i
  by_cases hi : i ∈ C
  · have he : (fun j => flip (fun _ => false) (C ×ˢ D) (i, j)) =
        flip (fun _ => false) D := by
      funext j
      simp [flip, hi]
    rw [he, hD']
    simp [flip, hi]
  · have he : (fun j => flip (fun _ => false) (C ×ˢ D) (i, j)) =
        fun _ => false := by
      funext j
      simp [flip, hi]
    rw [he, hg]
    simp [flip, hi]

section Finite
variable [Fintype I] [Fintype J]

theorem sensitivityAt_compose (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (x : I × J → Bool) :
    sensitivityAt (compose f g) x =
      ∑ i ∈ Finset.univ.filter (fun i =>
        f (flip (fun k => g (fun a => x (k, a))) {i}) ≠
          f (fun k => g (fun a => x (k, a)))),
        sensitivityAt g (fun a => x (i, a)) := by
  simp only [sensitivityAt, Finset.card_eq_sum_ones, Finset.sum_filter,
    compose_flip_sensitive_iff, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : f (flip (fun k => g (fun a => x (k, a))) {i}) ≠
      f (fun k => g (fun a => x (k, a)))
  · simp [hi]
  · simp [hi]

theorem sensitivity_compose_le (f : (I → Bool) → Bool) (g : (J → Bool) → Bool) :
    sensitivity (compose f g) ≤ sensitivity f * sensitivity g := by
  apply sensitivity_le
  intro x
  rw [sensitivityAt_compose]
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        f (flip (fun k => g (fun a => x (k, a))) {i}) ≠
          f (fun k => g (fun a => x (k, a)))), sensitivity g :=
      Finset.sum_le_sum fun i _ => sensitivityAt_le_sensitivity g _
    _ = sensitivityAt f (fun k => g (fun a => x (k, a))) * sensitivity g := by
      simp [sensitivityAt]
    _ ≤ sensitivity f * sensitivity g :=
      Nat.mul_le_mul_right _ (sensitivityAt_le_sensitivity f _)

theorem blockSensitivityAt_compose_zero_le (f : (I → Bool) → Bool)
    (g : (J → Bool) → Bool) (hg : g (fun _ => false) = false) :
    blockSensitivityAt f (fun _ => false) * blockSensitivityAt g (fun _ => false) ≤
      blockSensitivityAt (compose f g) (fun _ => false) := by
  obtain ⟨S, hS, hdS, hbS⟩ := exists_blockSensitivityAt_family f (fun _ => false)
  obtain ⟨T, hT, hdT, hbT⟩ := exists_blockSensitivityAt_family g (fun _ => false)
  have h := le_blockSensitivityAt_of_family (compose f g) (fun _ => false)
    (fun p : S × T => p.1.val ×ˢ p.2.val)
    (by
      intro p
      obtain ⟨i, hi⟩ := (hbS p.1.val p.1.property).1
      obtain ⟨j, hj⟩ := (hbT p.2.val p.2.property).1
      exact ⟨(i, j), Finset.mem_product.mpr ⟨hi, hj⟩⟩)
    (by
      intro p q hpq
      apply Finset.disjoint_left.mpr
      intro a ha hq
      obtain ⟨ha₁, ha₂⟩ := Finset.mem_product.mp ha
      obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
      by_cases hs : p.1 = q.1
      · have ht : p.2.val ≠ q.2.val := by
          intro h
          exact hpq (Prod.ext hs (Subtype.ext h))
        exact Finset.disjoint_left.mp (hdT _ p.2.property _ q.2.property ht) ha₂ hq₂
      · have hs' : p.1.val ≠ q.1.val := fun h => hs (Subtype.ext h)
        exact Finset.disjoint_left.mp (hdS _ p.1.property _ q.1.property hs') ha₁ hq₁)
    (by
      intro p
      rw [compose_flip_product_zero f g _ _ hg (hbT p.2.val p.2.property).2,
        compose_zero f g hg]
      exact (hbS p.1.val p.1.property).2)
  simpa only [Fintype.card_prod, Fintype.card_coe, hS, hT] using h

end Finite
end Paper320

end

end OAI

-- Reused in full from OpenAI, Reindex.lean

namespace OAI

/-! Coordinate equivalences preserve the two literal Boolean complexity measures. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J : Type}

theorem flip_reindex (e : I ≃ J) (x : J → Bool) (B : Finset I) :
    (fun i => flip x (B.map e.toEmbedding) (e i)) =
      flip (fun i => x (e i)) B := by
  funext i
  simp [flip]

theorem flip_reindex_singleton (e : I ≃ J) (x : J → Bool) (i : I) :
    (fun a => flip x {e i} (e a)) = flip (fun a => x (e a)) {i} := by
  simpa using flip_reindex e x {i}

section Finite
variable [Fintype I] [Fintype J]

theorem sensitivityAt_reindex (e : I ≃ J) (f : (I → Bool) → Bool) (x : J → Bool) :
    sensitivityAt (reindex e f) x = sensitivityAt f (fun i => x (e i)) := by
  have hs : (Finset.univ.filter fun j =>
      reindex e f (flip x {j}) ≠ reindex e f x).map e.symm.toEmbedding =
      Finset.univ.filter (fun i =>
        f (flip (fun a => x (e a)) {i}) ≠ f (fun a => x (e a))) := by
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change f (fun a => flip x {e i} (e a)) ≠ f (fun a => x (e a)) ↔ _
    rw [flip_reindex_singleton]
  simpa only [sensitivityAt, Finset.card_map] using congrArg Finset.card hs

theorem sensitivity_reindex (e : I ≃ J) (f : (I → Bool) → Bool) :
    sensitivity (reindex e f) = sensitivity f := by
  apply Nat.le_antisymm
  · apply sensitivity_le
    intro x
    rw [sensitivityAt_reindex]
    exact sensitivityAt_le_sensitivity f _
  · apply sensitivity_le
    intro x
    have h := sensitivityAt_le_sensitivity (reindex e f) (fun j => x (e.symm j))
    rw [sensitivityAt_reindex] at h
    simpa only [Equiv.symm_apply_apply] using h

theorem blockSensitivityAt_le_reindex (e : I ≃ J) (f : (I → Bool) → Bool)
    (x : J → Bool) :
    blockSensitivityAt f (fun i => x (e i)) ≤ blockSensitivityAt (reindex e f) x := by
  apply blockSensitivityAt_le
  intro blocks hd hb
  have h := le_blockSensitivityAt_of_family (reindex e f) x
    (fun B : blocks => B.val.map e.toEmbedding)
    (fun B => (hb B.val B.property).1.map (f := e.toEmbedding))
    (by
      intro A B hAB
      apply (Finset.disjoint_map e.toEmbedding).mpr
      exact hd A.val A.property B.val B.property (fun h => hAB (Subtype.ext h)))
    (by
      intro B
      change f (fun i => flip x (B.val.map e.toEmbedding) (e i)) ≠ _
      rw [flip_reindex]
      exact (hb B.val B.property).2)
  simpa only [Fintype.card_coe] using h

theorem blockSensitivityAt_reindex (e : I ≃ J) (f : (I → Bool) → Bool)
    (x : J → Bool) :
    blockSensitivityAt (reindex e f) x = blockSensitivityAt f (fun i => x (e i)) := by
  apply Nat.le_antisymm
  · have h := blockSensitivityAt_le_reindex e.symm (reindex e f) (fun i => x (e i))
    simpa only [Equiv.apply_symm_apply, reindex_symm] using h
  · exact blockSensitivityAt_le_reindex e f x

theorem blockSensitivity_reindex (e : I ≃ J) (f : (I → Bool) → Bool) :
    blockSensitivity (reindex e f) = blockSensitivity f := by
  apply Nat.le_antisymm
  · apply blockSensitivity_le
    intro x
    rw [blockSensitivityAt_reindex]
    exact blockSensitivityAt_le_blockSensitivity f _
  · apply blockSensitivity_le
    intro x
    have h := blockSensitivityAt_le_blockSensitivity (reindex e f) (fun j => x (e.symm j))
    rw [blockSensitivityAt_reindex] at h
    simpa only [Equiv.symm_apply_apply] using h

end Finite
end Paper320

end

end OAI

-- Reused in full from OpenAI, Or.lean

namespace OAI

/-! Balancing the zero and one sensitivities by an OR of disjoint copies. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320

variable {I K : Type} [Fintype K]

theorem orBits_flip_of_witness (x : K → Bool) {i j : K}
    (hji : j ≠ i) (hj : x j = true) : orBits (flip x {i}) = orBits x := by
  have h₁ : orBits x = true := (orBits_eq_true x).mpr ⟨j, hj⟩
  have h₂ : orBits (flip x {i}) = true :=
    (orBits_eq_true _).mpr ⟨j, by rw [flip_singleton_other x hji, hj]⟩
  exact h₂.trans h₁.symm

theorem orCopies_zero (f : (I → Bool) → Bool) (hf : f (fun _ => false) = false) :
    orCopies (K := K) f (fun _ => false) = false := by
  rw [orCopies, compose_zero _ _ hf, orBits_zero]

variable [Fintype I]

theorem sensitivity_orCopies_le (f : (I → Bool) → Bool) (S₀ S₁ : ℕ)
    (h₀ : ∀ x, f x = false → sensitivityAt f x ≤ S₀)
    (h₁ : ∀ x, f x = true → sensitivityAt f x ≤ S₁) :
    sensitivity (orCopies (K := K) f) ≤ max (Fintype.card K * S₀) S₁ := by
  apply sensitivity_le
  intro x
  change sensitivityAt (compose orBits f) x ≤ _
  rw [sensitivityAt_compose]
  let y : K → Bool := fun k => f (fun a => x (k, a))
  let s : Finset K := Finset.univ.filter fun i => orBits (flip y {i}) ≠ orBits y
  change (∑ i ∈ s, sensitivityAt f (fun a => x (i, a))) ≤ _
  by_cases hy : orBits y = false
  · have hall := (orBits_eq_false y).mp hy
    calc
      _ ≤ ∑ _i ∈ s, S₀ := Finset.sum_le_sum fun i _ => h₀ _ (hall i)
      _ = s.card * S₀ := by simp
      _ ≤ Fintype.card K * S₀ := Nat.mul_le_mul_right _ (Finset.card_le_univ _)
      _ ≤ max (Fintype.card K * S₀) S₁ := le_max_left _ _
  · have htrue : orBits y = true := by cases h : orBits y <;> simp_all
    obtain ⟨i, hi⟩ := (orBits_eq_true y).mp htrue
    have hs : s ⊆ {i} := by
      intro j hj
      have hc := (Finset.mem_filter.mp hj).2
      by_contra hji
      have hij : i ≠ j := Ne.symm (by simpa only [Finset.mem_singleton] using hji)
      exact hc (orBits_flip_of_witness y hij hi)
    calc
      _ ≤ ∑ j ∈ ({i} : Finset K), sensitivityAt f (fun a => x (j, a)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; exact Nat.zero_le _)
      _ = sensitivityAt f (fun a => x (i, a)) := by simp
      _ ≤ S₁ := h₁ _ hi
      _ ≤ max (Fintype.card K * S₀) S₁ := le_max_right _ _

theorem card_le_blockSensitivityAt_orBits_zero :
    Fintype.card K ≤ blockSensitivityAt (orBits (K := K)) (fun _ => false) := by
  apply le_blockSensitivityAt_of_family orBits (fun _ => false) (fun k : K => {k})
  · intro k
    simp
  · intro k l hkl
    simpa using hkl
  · intro k
    have h : orBits (flip (fun _ : K => false) {k}) = true :=
      (orBits_eq_true _).mpr ⟨k, by simp⟩
    simp [h]

theorem blockSensitivityAt_orCopies_zero (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) :
    Fintype.card K * blockSensitivityAt f (fun _ => false) ≤
      blockSensitivityAt (orCopies (K := K) f) (fun _ => false) := by
  exact (Nat.mul_le_mul_right _ card_le_blockSensitivityAt_orBits_zero).trans
    (blockSensitivityAt_compose_zero_le orBits f hf)

end Paper320

end

end OAI

-- Reused in full from OpenAI, Iterates.lean

namespace OAI

/-! Repeated disjoint composition with explicit finite raw-coordinate types. -/

noncomputable section
open scoped Classical

namespace Paper320

def iterateCompose {I : Type} (f : (I → Bool) → Bool) :
    (m : ℕ) → (IterateCoord I m → Bool) → Bool
  | 0 => fun x => x ()
  | m + 1 => compose f (iterateCompose f m)

theorem iterateCompose_one {I : Type} (f : (I → Bool) → Bool)
    (x : IterateCoord I 1 → Bool) :
    iterateCompose f 1 x = f (fun i => x (i, ())) := rfl

theorem iterateCompose_zero {I : Type} (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) (m : ℕ) :
    iterateCompose f m (fun _ => false) = false := by
  induction m with
  | zero => rfl
  | succ m ih => exact (compose_zero f (iterateCompose f m) ih).trans hf

variable {I : Type} [Fintype I]

theorem iterateCoord_card (m : ℕ) :
    Fintype.card (IterateCoord I m) = Fintype.card I ^ m := by
  induction m with
  | zero => exact Fintype.card_unique
  | succ m ih =>
    change Fintype.card (I × IterateCoord I m) = _
    rw [Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

theorem sensitivity_iterateCompose_le (f : (I → Bool) → Bool) (m : ℕ) :
    sensitivity (iterateCompose f m) ≤ sensitivity f ^ m := by
  induction m with
  | zero =>
    apply sensitivity_le
    intro x
    exact (sensitivityAt_le_card (iterateCompose f 0) x).trans_eq (iterateCoord_card 0)
  | succ m ih =>
    change sensitivity (compose f (iterateCompose f m)) ≤ _
    calc
      _ ≤ sensitivity f * sensitivity (iterateCompose f m) := sensitivity_compose_le _ _
      _ ≤ sensitivity f * sensitivity f ^ m := Nat.mul_le_mul_left _ ih
      _ = sensitivity f ^ (m + 1) := by rw [pow_succ, Nat.mul_comm]

theorem blockSensitivityAt_iterateCompose_zero (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) (m : ℕ) :
    blockSensitivityAt f (fun _ => false) ^ m ≤
      blockSensitivityAt (iterateCompose f m) (fun _ => false) := by
  induction m with
  | zero =>
    have h := le_blockSensitivityAt (iterateCompose f 0) (fun _ => false)
      ({{()}} : Finset (Finset Unit))
      (by
        intro A hA B hB hne
        exact (hne ((Finset.mem_singleton.mp hA).trans (Finset.mem_singleton.mp hB).symm)).elim)
      (by
        intro B hB
        have hB' : B = {()} := Finset.mem_singleton.mp hB
        subst B
        exact ⟨Finset.singleton_nonempty _, by simp [iterateCompose, flip]⟩)
    simpa only [Finset.card_singleton, pow_zero] using h
  | succ m ih =>
    change _ ≤ blockSensitivityAt (compose f (iterateCompose f m)) (fun _ => false)
    calc
      _ = blockSensitivityAt f (fun _ => false) *
          blockSensitivityAt f (fun _ => false) ^ m := by rw [pow_succ, Nat.mul_comm]
      _ ≤ blockSensitivityAt f (fun _ => false) *
          blockSensitivityAt (iterateCompose f m) (fun _ => false) := Nat.mul_le_mul_left _ ih
      _ ≤ _ := blockSensitivityAt_compose_zero_le f (iterateCompose f m)
        (iterateCompose_zero f hf m)

def iterateFin (f : (I → Bool) → Bool) (m : ℕ) :
    (Fin (Fintype.card I ^ m) → Bool) → Bool :=
  reindex (Fintype.equivFinOfCardEq (iterateCoord_card (I := I) m)) (iterateCompose f m)

theorem iterateFin_zero (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) (m : ℕ) :
    iterateFin f m (fun _ => false) = false :=
  iterateCompose_zero f hf m

theorem sensitivity_iterateFin_le (f : (I → Bool) → Bool) (m : ℕ) :
    sensitivity (iterateFin f m) ≤ sensitivity f ^ m := by
  rw [iterateFin, sensitivity_reindex]
  exact sensitivity_iterateCompose_le f m

theorem blockSensitivityAt_iterateFin_zero (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) (m : ℕ) :
    blockSensitivityAt f (fun _ => false) ^ m ≤
      blockSensitivityAt (iterateFin f m) (fun _ => false) := by
  rw [iterateFin, blockSensitivityAt_reindex]
  exact blockSensitivityAt_iterateCompose_zero f hf m

theorem nonconstant_of_blockSensitivityAt_pos (f : (I → Bool) → Bool) (x : I → Bool)
    (h : 0 < blockSensitivityAt f x) : ∃ y z, f y ≠ f z := by
  obtain ⟨blocks, hc, _, hb⟩ := exists_blockSensitivityAt_family f x
  have hn : blocks.Nonempty := Finset.card_pos.mp (hc.symm ▸ h)
  obtain ⟨B, hB⟩ := hn
  exact ⟨flip x B, x, (hb B hB).2⟩

theorem iterateFin_nonconstant (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false)
    (h : 0 < blockSensitivityAt f (fun _ => false)) (m : ℕ) :
    ∃ x y, iterateFin f m x ≠ iterateFin f m y := by
  exact nonconstant_of_blockSensitivityAt_pos _ _
    ((pow_pos h m).trans_le (blockSensitivityAt_iterateFin_zero f hf m))

end Paper320

end

end OAI

namespace SensitivityCampaign
noncomputable section
open scoped Classical
open OAI.Paper320

private def translate {I : Type} (x y : I → Bool) : I → Bool :=
  fun i => Bool.xor (x i) (y i)

private lemma translate_zero {I : Type} (x : I → Bool) :
    translate x (fun _ => false) = x := by
  funext i
  simp [translate]

private lemma translate_flip {I : Type} (x y : I → Bool) (B : Finset I) :
    translate x (flip y B) = flip (translate x y) B := by
  funext i
  by_cases hi : i ∈ B
  · cases hx : x i <;> cases hy : y i <;> simp [translate, OAI.Paper320.flip, hi, hx, hy]
  · simp [translate, OAI.Paper320.flip, hi]

private def normalize {I : Type} (f : (I → Bool) → Bool) (x : I → Bool) :
    (I → Bool) → Bool := fun y => Bool.xor (f (translate x y)) (f x)

private lemma normalize_zero {I : Type} (f : (I → Bool) → Bool) (x : I → Bool) :
    normalize f x (fun _ => false) = false := by
  simp [normalize, translate_zero]

private lemma normalize_flip_ne {I : Type} (f : (I → Bool) → Bool) (x y : I → Bool)
    (B : Finset I) :
    normalize f x (flip y B) ≠ normalize f x y ↔
      f (flip (translate x y) B) ≠ f (translate x y) := by
  unfold normalize
  rw [translate_flip]
  cases h : f x <;> simp [h]

private lemma sensitivity_normalize_le {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) :
    sensitivity (normalize f x) ≤ sensitivity f := by
  apply sensitivity_le
  intro y
  have he : sensitivityAt (normalize f x) y = sensitivityAt f (translate x y) := by
    simp only [sensitivityAt, normalize_flip_ne]
  rw [he]
  exact sensitivityAt_le_sensitivity f _

private lemma blockSensitivityAt_normalize_zero {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) :
    blockSensitivityAt (normalize f x) (fun _ => false) = blockSensitivityAt f x := by
  simp only [blockSensitivityAt, normalize_flip_ne, translate_zero]

private lemma exists_zero_sensitive {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (hnc : ∃ x y, f x ≠ f y) :
    ∃ x i, f x = false ∧ f (flip x {i}) = true := by
  obtain ⟨x, hx⟩ := exists_sensitivityAt_eq f
  have hp : 0 < sensitivityAt f x := hx.symm ▸ sensitivity_pos_of_nonconstant f hnc
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hp
  have hn := (Finset.mem_filter.mp hi).2
  cases hfx : f x with
  | false =>
    refine ⟨x, i, hfx, ?_⟩
    cases hfi : f (flip x {i}) <;> simp_all
  | true =>
    refine ⟨flip x {i}, i, ?_, ?_⟩
    · cases hfi : f (flip x {i}) <;> simp_all
    · simpa using hfx

private lemma sensitivity_orCopies_lower {I K : Type} [Fintype I] [Fintype K]
    (f : (I → Bool) → Bool) (hnc : ∃ x y, f x ≠ f y) :
    Fintype.card K ≤ sensitivity (orCopies (K := K) f) := by
  obtain ⟨x, i, hx, hi⟩ := exists_zero_sensitive f hnc
  let y : K × I → Bool := fun p => x p.2
  have hs (k : K) : orCopies (K := K) f (flip y {(k, i)}) ≠ orCopies f y := by
    apply (compose_flip_sensitive_iff orBits f y k i).mpr
    constructor
    · simpa [y, hx, hi]
    · have hzero : (fun k : K => f (fun a => y (k, a))) = fun _ => false := by
        funext k
        exact hx
      rw [hzero, orBits_zero]
      have ht : orBits (flip (fun _ : K => false) {k}) = true :=
        (orBits_eq_true _).mpr ⟨k, by simp⟩
      simp [ht]
  have hsub : (Finset.univ.image fun k : K => (k, i)) ⊆
      Finset.univ.filter (fun p => orCopies (K := K) f (flip y {p}) ≠ orCopies f y) := by
    intro p hp
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs k⟩
  have hc := Finset.card_le_card hsub
  have hinj : Function.Injective (fun k : K => (k, i)) := by
    intro k l h
    exact congrArg Prod.fst h
  have hh : Fintype.card K ≤ sensitivityAt (orCopies (K := K) f) y := by
    simpa only [sensitivityAt, Finset.card_image_of_injective _ hinj, Finset.card_univ] using hc
  exact hh.trans (sensitivityAt_le_sensitivity _ _)

end
end SensitivityCampaign

namespace SensitivityCampaign
noncomputable section
open scoped Classical
open OAI.Paper320

private lemma amplified_copies {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (hf : f (fun _ => false) = false)
    (A B : ℕ) (hB : 1 < B) (hs : sensitivity f ≤ A)
    (hb : B ≤ blockSensitivityAt f (fun _ => false))
    (S : ℕ) (hS : 2 ≤ S) (m : ℕ) :
    ∃ (n : ℕ) (g : (Fin n → Bool) → Bool),
      S ≤ sensitivity g ∧ sensitivity g ≤ S * A ^ m ∧ B ^ m ≤ blockSensitivity g := by
  let h := iterateFin f m
  have hz : h (fun _ => false) = false := iterateFin_zero f hf m
  have hn : ∃ x y, h x ≠ h y := iterateFin_nonconstant f hf (by omega) m
  have hs' : sensitivity h ≤ A ^ m := by
    have hp : sensitivity f ^ m ≤ A ^ m := by gcongr
    exact (sensitivity_iterateFin_le f m).trans hp
  have hb' : B ^ m ≤ blockSensitivityAt h (fun _ => false) := by
    have hp : B ^ m ≤ blockSensitivityAt f (fun _ => false) ^ m := by gcongr
    exact hp.trans (blockSensitivityAt_iterateFin_zero f hf m)
  let F := orCopies (K := Fin S) h
  let e := Fintype.equivFin (Fin S × Fin (Fintype.card I ^ m))
  refine ⟨_, reindex e F, ?_, ?_, ?_⟩
  · rw [sensitivity_reindex]
    simpa only [Fintype.card_fin] using sensitivity_orCopies_lower (K := Fin S) h hn
  · rw [sensitivity_reindex]
    have hm : sensitivity h ≤ S * sensitivity h := by nlinarith
    have hc := sensitivity_orCopies_le (K := Fin S) h (sensitivity h) (sensitivity h)
      (fun x _ => sensitivityAt_le_sensitivity h x)
      (fun x _ => sensitivityAt_le_sensitivity h x)
    simp only [Fintype.card_fin, max_eq_left hm] at hc
    exact hc.trans (Nat.mul_le_mul_left S hs')
  · rw [blockSensitivity_reindex]
    have hc := blockSensitivityAt_orCopies_zero (K := Fin S) h hz
    simp only [Fintype.card_fin] at hc
    have hm : blockSensitivityAt h (fun _ => false) ≤
        S * blockSensitivityAt h (fun _ => false) := by nlinarith
    exact hb'.trans (hm.trans (hc.trans (blockSensitivityAt_le_blockSensitivity F _)))

private theorem finite_certificate_proof
    {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (A B : ℕ) (a : ℝ)
    (hA : 1 < A) (hB : 1 < B) (ha : 0 ≤ a)
    (hs : sensitivity f ≤ A) (hb : B ≤ blockSensitivityAt f x)
    (hpow : (A : ℝ) ^ a ≤ (B : ℝ)) : AchievesExponent a := by
  let f₀ := normalize f x
  have hz : f₀ (fun _ => false) = false := normalize_zero f x
  have hs₀ : sensitivity f₀ ≤ A := (sensitivity_normalize_le f x).trans hs
  have hb₀ : B ≤ blockSensitivityAt f₀ (fun _ => false) := by
    simpa only [f₀, blockSensitivityAt_normalize_zero] using hb
  intro ε hε S hS
  have hSr : (1 : ℝ) ≤ S := by exact_mod_cast (show 1 ≤ S by omega)
  have hAr : (1 : ℝ) < A := by exact_mod_cast hA
  have hAp : (0 : ℝ) < A := by linarith
  by_cases he : a ≤ ε
  · obtain ⟨N, g, hgs, _, hgb⟩ := amplified_copies f₀ hz A B hB hs₀ hb₀ S hS 0
    refine ⟨N, g, hgs, ?_⟩
    have hg1 : (1 : ℝ) ≤ sensitivity g := by exact_mod_cast (show 1 ≤ sensitivity g by omega)
    have hb1 : (1 : ℝ) ≤ blockSensitivity g := by exact_mod_cast hgb
    exact (Real.rpow_le_one_of_one_le_of_nonpos hg1 (by linarith)).trans hb1
  · have hepos : 0 < a - ε := by linarith
    have hbase : (1 : ℝ) < (A : ℝ) ^ ε := Real.one_lt_rpow hAr hε
    have ht := tendsto_pow_atTop_atTop_of_one_lt hbase
    obtain ⟨m, hm⟩ := (ht.eventually (Filter.eventually_ge_atTop ((S : ℝ) ^ a))).exists
    obtain ⟨N, g, hgs, hgu, hgb⟩ := amplified_copies f₀ hz A B hB hs₀ hb₀ S hS m
    refine ⟨N, g, hgs, ?_⟩
    have hgur : (sensitivity g : ℝ) ≤ (S : ℝ) * (A : ℝ) ^ m := by exact_mod_cast hgu
    have hgbr : (B : ℝ) ^ m ≤ (blockSensitivity g : ℝ) := by exact_mod_cast hgb
    have hcomm : ((A : ℝ) ^ m) ^ (a - ε) = ((A : ℝ) ^ (a - ε)) ^ m := by
      rw [← Real.rpow_natCast_mul hAp.le, mul_comm (m : ℝ), Real.rpow_mul_natCast hAp.le]
    calc
      (sensitivity g : ℝ) ^ (a - ε) ≤ ((S : ℝ) * (A : ℝ) ^ m) ^ (a - ε) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hgur hepos.le
      _ = (S : ℝ) ^ (a - ε) * ((A : ℝ) ^ (a - ε)) ^ m := by
        rw [Real.mul_rpow (Nat.cast_nonneg _) (pow_nonneg hAp.le _), hcomm]
      _ ≤ (S : ℝ) ^ a * ((A : ℝ) ^ (a - ε)) ^ m := by
        apply mul_le_mul_of_nonneg_right
        · exact Real.rpow_le_rpow_of_exponent_le hSr (by linarith)
        · positivity
      _ ≤ ((A : ℝ) ^ ε) ^ m * ((A : ℝ) ^ (a - ε)) ^ m := by
        exact mul_le_mul_of_nonneg_right hm (by positivity)
      _ = ((A : ℝ) ^ a) ^ m := by
        rw [← mul_pow, ← Real.rpow_add hAp]
        have hex : ε + (a - ε) = a := by ring
        rw [hex]
      _ ≤ (B : ℝ) ^ m := pow_le_pow_left₀ (Real.rpow_nonneg hAp.le _) hpow m
      _ ≤ (blockSensitivity g : ℝ) := hgbr

end
end SensitivityCampaign

open OAI.Paper320

theorem SensitivityCampaign.finite_certificate
    {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (A B : ℕ) (a : ℝ)
    (hA : 1 < A) (hB : 1 < B) (ha : 0 ≤ a)
    (hs : sensitivity f ≤ A) (hb : B ≤ blockSensitivityAt f x)
    (hpow : (A : ℝ) ^ a ≤ (B : ℝ)) :
    SensitivityCampaign.AchievesExponent a :=
  SensitivityCampaign.finite_certificate_proof f x A B a hA hB ha hs hb hpow

end Component0

-- Source component: Theorems/Thm_OAI_Paper320_rowClause_repair_cases.lean
section Component1
-- Accepted Prove2Me submission 00fdf387-df9d-450f-92b5-63d564786000
-- Local packaging: deduplicated identical-name helpers; retained their first accepted proof.
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/RecursiveRepair.lean:L35-L97
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.rowClause_repair_cases. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.

-- ---- from OAI.Combinatorics.Sensitivity.Basic ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Finite Boolean flips and the exact maximum/witness interfaces for sensitivity. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J K : Type}

section Finite

variable [Fintype I]

end Finite
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Tournament ----
namespace OAI

/-! Finite tournaments and the target-constant labeling condition. -/

noncomputable section
open scoped Classical

namespace Paper320

namespace Tournament
variable {k : ℕ} (T : Tournament k)

theorem ne_of_adj {i j : Fin k} (h : T.Adj i j) : i ≠ j := by
  rintro rfl
  exact T.loopless i h

end Tournament

namespace GoodLabeling
variable {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)

end GoodLabeling
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveDefinitions ----
namespace OAI

/-! The literal target-row and labeled-gate construction. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem rowClause_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    rowClause T label F q x i = true ↔
      (∀ c, F (Fin.last h) (recursiveChild x i c) = true) ∧
      ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false := by
  simp only [rowClause, decide_eq_true_eq]

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveFlips ----
namespace OAI

/-! A raw bit belongs to one child and changes at most one condition of a clause. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursiveChild_flip_same {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) (a : I) :
    recursiveChild (flip x {((j, c), a)}) j c = flip (recursiveChild x j c) {a} :=
  flip_prod_same x (j, c) a

theorem recursiveChild_flip_other {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j j' : Fin k) (c c' : Fin r) (a : I)
    (h : (j', c') ≠ (j, c)) :
    recursiveChild (flip x {((j, c), a)}) j' c' = recursiveChild x j' c' :=
  flip_prod_other x a h

theorem rowClause_eq_of_conditions {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x y : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (ht : ∀ c, F (Fin.last h) (recursiveChild x i c) =
      F (Fin.last h) (recursiveChild y i c))
    (hg : ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) =
      F (gateIndex q) (recursiveChild y j (label i j))) :
    rowClause T label F q x i = rowClause T label F q y i := by
  apply Bool.eq_iff_iff.mpr
  rw [rowClause_eq_true_iff, rowClause_eq_true_iff]
  constructor
  · rintro ⟨hxt, hxg⟩
    exact ⟨fun c => (ht c).symm.trans (hxt c),
      fun j hij => (hg j hij).symm.trans (hxg j hij)⟩
  · rintro ⟨hyt, hyg⟩
    exact ⟨fun c => (ht c).trans (hyt c),
      fun j hij => (hg j hij).trans (hyg j hij)⟩

theorem rowClause_flip_eq {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) (c : Fin r) (a : I)
    (ht : j = i → F (Fin.last h) (flip (recursiveChild x j c) {a}) =
      F (Fin.last h) (recursiveChild x j c))
    (hg : T.Adj i j → c = label i j →
      F (gateIndex q) (flip (recursiveChild x j c) {a}) =
        F (gateIndex q) (recursiveChild x j c)) :
    rowClause T label F q (flip x {((j, c), a)}) i = rowClause T label F q x i := by
  apply rowClause_eq_of_conditions
  · intro c'
    by_cases heq : (i, c') = (j, c)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [recursiveChild_flip_same]
      exact ht rfl
    · rw [recursiveChild_flip_other x j i c c' a heq]
  · intro j' hij'
    by_cases heq : (j', label i j') = (j, c)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [recursiveChild_flip_same]
      exact hg hij' rfl
    · rw [recursiveChild_flip_other x j j' c (label i j') a heq]

theorem rowClause_flip_change {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) (c : Fin r) (a : I)
    (hc : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i) :
    (j = i ∧ F (Fin.last h) (flip (recursiveChild x j c) {a}) ≠
      F (Fin.last h) (recursiveChild x j c)) ∨
    (T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (flip (recursiveChild x j c) {a}) ≠
        F (gateIndex q) (recursiveChild x j c)) := by
  by_contra hn
  apply hc
  apply rowClause_flip_eq
  · intro hji
    by_contra hne
    exact hn (Or.inl ⟨hji, hne⟩)
  · intro hij hcl
    by_contra hne
    exact hn (Or.inr ⟨hij, hcl, hne⟩)

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveRepair ----
namespace OAI

/-! A successful raw-bit flip repairs the unique initial failed condition. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem repaired_target_location {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (c c' : Fin r) (a : I)
    (hf : rowClause T label F q (flip x {((j, c), a)}) i = true)
    (hz : F (Fin.last h) (recursiveChild x i c') = false) : (i, c') = (j, c) := by
  by_contra hne
  have ht := ((rowClause_eq_true_iff T label F q _ i).mp hf).1 c'
  rw [recursiveChild_flip_other x j i c c' a hne, hz] at ht
  exact Bool.false_ne_true ht

theorem repaired_gate_location {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j j' : Fin k) (c : Fin r) (a : I)
    (hf : rowClause T label F q (flip x {((j, c), a)}) i = true)
    (hij' : T.Adj i j') (hon : F (gateIndex q) (recursiveChild x j' (label i j')) = true) :
    (j', label i j') = (j, c) := by
  by_contra hne
  have hg := ((rowClause_eq_true_iff T label F q _ i).mp hf).2 j' hij'
  rw [recursiveChild_flip_other x j j' c (label i j') a hne, hon] at hg
  exact Bool.false_ne_true hg.symm

theorem rowClause_repair_cases {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (c : Fin r) (a : I)
    (hi : rowClause T label F q x i = false)
    (hf : rowClause T label F q (flip x {((j, c), a)}) i = true) :
    (i ∈ targetCandidates T label F q x ∧ j = i ∧
      F (Fin.last h) (recursiveChild x j c) = false ∧
      F (Fin.last h) (flip (recursiveChild x j c) {a}) = true) ∨
    (i ∈ gateCandidates T label F q x ∧ T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (recursiveChild x j c) = true ∧
      F (gateIndex q) (flip (recursiveChild x j c) {a}) = false) := by
  have hchange : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i := by
    simp [hi, hf]
  rcases rowClause_flip_change T label F q x i j c a hchange with
    ⟨hji, ht⟩ | ⟨hij, rfl, hg⟩
  · subst j
    have hton := ((rowClause_eq_true_iff T label F q _ i).mp hf).1 c
    rw [recursiveChild_flip_same] at hton
    have htoff : F (Fin.last h) (recursiveChild x i c) = false := by
      cases hc : F (Fin.last h) (recursiveChild x i c)
      · rfl
      · exact False.elim (ht (hton.trans hc.symm))
    have htargets : targetFailures F x i = {c} := by
      ext c'
      simp only [targetFailures, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hfalse
        exact congrArg Prod.snd (repaired_target_location T label F q x i i c c' a hf hfalse)
      · rintro rfl
        exact htoff
    have hgates : gateFailures T label F q x i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j' hj'
      have h := (Finset.mem_filter.mp hj').2
      have heq := repaired_gate_location T label F q x i i j' c a hf h.1 h.2
      exact T.ne_of_adj h.1 (congrArg Prod.fst heq).symm
    have hmem : i ∈ targetCandidates T label F q x := by
      simp [targetCandidates, htargets, hgates]
    exact Or.inl ⟨hmem, rfl, htoff, hton⟩
  · have hgoff := ((rowClause_eq_true_iff T label F q _ i).mp hf).2 j hij
    rw [recursiveChild_flip_same] at hgoff
    have hgon : F (gateIndex q) (recursiveChild x j (label i j)) = true := by
      cases hc : F (gateIndex q) (recursiveChild x j (label i j))
      · exact False.elim (hg (hgoff.trans hc.symm))
      · rfl
    have htargets : targetFailures F x i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c' hc'
      have heq := repaired_target_location T label F q x i j (label i j) c' a hf
        (Finset.mem_filter.mp hc').2
      exact T.ne_of_adj hij (congrArg Prod.fst heq)
    have hgates : gateFailures T label F q x i = {j} := by
      ext j'
      simp only [gateFailures, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hij', hon⟩
        exact congrArg Prod.fst (repaired_gate_location T label F q x i j j' (label i j) a hf hij' hon)
      · rintro rfl
        exact ⟨hij, hgon⟩
    have hmem : i ∈ gateCandidates T label F q x := by
      simp [gateCandidates, htargets, hgates]
    exact Or.inr ⟨hmem, hij, rfl, hgon, hgoff⟩

end Paper320

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320
open scoped Classical


end Component1

-- Source component: Theorems/Thm_OAI_Paper320_recursive_joint_one_at.lean
section Component2
-- Accepted Prove2Me submission 16f88b49-a7f7-4ae4-b991-ce77b96b8fa9
-- Local packaging: deduplicated identical-name helpers; retained their first accepted proof.
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/RecursiveOne.lean:L72-L135
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.recursive_joint_one_at. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveProfiles ----
namespace OAI

/-! The side and joint profiles count literal flips of the same raw input. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem NestedFamily.rejects_of_le {h : ℕ} {I : Type}
    {F : Fin h → (I → Bool) → Bool} (hF : NestedFamily F)
    {q q' : Fin h} {x} (hqq : q ≤ q') (hx : F q x = false) :
    F q' x = false := by
  cases h' : F q' x
  · rfl
  · have := hF.accepts_of_le hqq h'
    simp [hx] at this

theorem sensitivityAt_le_sideSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (q : Fin h) (x : I → Bool)
    (hx : F q x = b) : sensitivityAt (F q) x ≤ sideSensitivity F b := by
  apply Finset.le_sup_of_le (Finset.mem_univ q)
  apply Finset.le_sup_of_le (Finset.mem_univ x)
  simp [hx]

theorem jointSensitivityAt_le_jointSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (q q' : Fin h) (x : I → Bool)
    (hqq : q < q') (hx : F q x = b) (hx' : F q' x = b) :
    jointSensitivityAt (F q) (F q') x ≤ jointSensitivity F b := by
  apply Finset.le_sup_of_le (Finset.mem_univ q)
  apply Finset.le_sup_of_le (Finset.mem_univ q')
  apply Finset.le_sup_of_le (Finset.mem_univ x)
  simp [hqq, hx, hx']

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Basic ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Finite Boolean flips and the exact maximum/witness interfaces for sensitivity. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J K : Type}

section Finite

variable [Fintype I]

end Finite
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Tournament ----
namespace OAI

/-! Finite tournaments and the target-constant labeling condition. -/

noncomputable section
open scoped Classical

namespace Paper320

namespace Tournament
variable {k : ℕ} (T : Tournament k)

end Tournament

namespace GoodLabeling
variable {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)

end GoodLabeling
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveDefinitions ----
namespace OAI

/-! The literal target-row and labeled-gate construction. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem gateIndex_antitone {h : ℕ} {q q' : Fin h} (hqq : q ≤ q') :
    gateIndex q' ≤ gateIndex q := by
  exact Fin.rev_le_rev.mpr hqq

theorem gateIndex_strictAnti {h : ℕ} {q q' : Fin h} (hqq : q < q') :
    gateIndex q' < gateIndex q := by
  exact Fin.rev_lt_rev.mpr hqq

theorem recursiveFamily_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = true ↔ ∃ i, rowClause T label F q x i = true := by
  simp only [recursiveFamily, decide_eq_true_eq]

theorem recursiveFamily_eq_false_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = false ↔ ∀ i, rowClause T label F q x i = false := by
  simp [recursiveFamily]

theorem rowClause_nested {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) {q q' : Fin h} (hqq : q ≤ q')
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : rowClause T label F q' x i = true) : rowClause T label F q x i = true := by
  rw [rowClause_eq_true_iff] at hi ⊢
  refine ⟨hi.1, fun j hij => ?_⟩
  exact hF.rejects_of_le (gateIndex_antitone hqq) (hi.2 j hij)

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveFlips ----
namespace OAI

/-! A raw bit belongs to one child and changes at most one condition of a clause. -/

noncomputable section
open scoped Classical

namespace Paper320

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveSets ----
namespace OAI

/-! Finite sets of changing raw coordinates inside an individual child. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem card_biUnion_le_mul {J I : Type} [DecidableEq I] (A : Finset J) (B : J → Finset I) (n : ℕ)
    (hn : ∀ j ∈ A, (B j).card ≤ n) : (A.biUnion B).card ≤ A.card * n := by
  calc
    (A.biUnion B).card ≤ ∑ j ∈ A, (B j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ A, n := Finset.sum_le_sum hn
    _ = A.card * n := by simp

theorem rowClause_joint_flip_change {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q q' : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (c : Fin r) (a : I)
    (hc : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i)
    (hc' : rowClause T label F q' (flip x {((j, c), a)}) i ≠ rowClause T label F q' x i) :
    (j = i ∧ F (Fin.last h) (flip (recursiveChild x j c) {a}) ≠
      F (Fin.last h) (recursiveChild x j c)) ∨
    (T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (flip (recursiveChild x j c) {a}) ≠
        F (gateIndex q) (recursiveChild x j c) ∧
      F (gateIndex q') (flip (recursiveChild x j c) {a}) ≠
        F (gateIndex q') (recursiveChild x j c)) := by
  rcases rowClause_flip_change T label F q x i j c a hc with ht | ⟨hij, hcl, hq⟩
  · exact Or.inl ht
  · rcases rowClause_flip_change T label F q' x i j c a hc' with ht | hg
    · exact False.elim ((T.ne_of_adj hij) ht.1.symm)
    · exact Or.inr ⟨hij, hcl, hq, hg.2.2⟩

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveOne ----
namespace OAI

/-! The two recurrences for inputs at which the parent predicates accept. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursive_joint_one_at {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o)
    (q q' : Fin h) (hqq : q < q') (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T label F q x = true)
    (hx' : recursiveFamily T label F q' x = true) :
    jointSensitivityAt (recursiveFamily T label F q) (recursiveFamily T label F q') x ≤
      o * jointSensitivity F false + r * sideSensitivity F true := by
  obtain ⟨i, hi'⟩ := (recursiveFamily_eq_true_iff T label F q' x).mp hx'
  have hi := rowClause_nested T label F hF hqq.le x i hi'
  have hcond := (rowClause_eq_true_iff T label F q x i).mp hi
  have hcond' := (rowClause_eq_true_iff T label F q' x i).mp hi'
  let U := Finset.univ.biUnion fun c => childChanges F (Fin.last h) x i c
  let V := (Finset.univ.filter (T.Adj i)).biUnion fun j =>
    childJointChanges F (gateIndex q') (gateIndex q) x j (label i j)
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T label F q (flip x {p}) ≠ recursiveFamily T label F q x ∧
      recursiveFamily T label F q' (flip x {p}) ≠ recursiveFamily T label F q' x) ⊆ U ∪ V := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    have hchange := (Finset.mem_filter.mp hp).2
    have hf : recursiveFamily T label F q (flip x {((j, c), a)}) = false := by
      cases hy : recursiveFamily T label F q (flip x {((j, c), a)})
      · rfl
      · exact False.elim (hchange.1 (hy.trans hx.symm))
    have hf' : recursiveFamily T label F q' (flip x {((j, c), a)}) = false := by
      cases hy : recursiveFamily T label F q' (flip x {((j, c), a)})
      · rfl
      · exact False.elim (hchange.2 (hy.trans hx'.symm))
    have hif := (recursiveFamily_eq_false_iff T label F q _).mp hf i
    have hif' := (recursiveFamily_eq_false_iff T label F q' _).mp hf' i
    have hic : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i := by
      simp [hi, hif]
    have hic' : rowClause T label F q' (flip x {((j, c), a)}) i ≠ rowClause T label F q' x i := by
      simp [hi', hif']
    rcases rowClause_joint_flip_change T label F q q' x i j c a hic hic' with
      ⟨rfl, ht⟩ | ⟨hij, rfl, hg, hg'⟩
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨c, Finset.mem_univ _, by simpa [childChanges] using ht⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
        by simpa [childJointChanges] using And.intro hg' hg⟩
  have hU : U.card ≤ r * sideSensitivity F true := by
    simpa [U] using card_biUnion_le_mul Finset.univ
      (fun c => childChanges F (Fin.last h) x i c) (sideSensitivity F true)
      (fun c _ => by
        rw [childChanges_card]
        exact sensitivityAt_le_sideSensitivity F true _ _ (hcond.1 c))
  have hV : V.card ≤ o * jointSensitivity F false := by
    simpa only [V, ho i] using card_biUnion_le_mul (Finset.univ.filter (T.Adj i))
      (fun j => childJointChanges F (gateIndex q') (gateIndex q) x j (label i j))
      (jointSensitivity F false) (fun j hj => by
        have hij := (Finset.mem_filter.mp hj).2
        rw [childJointChanges_card]
        exact jointSensitivityAt_le_jointSensitivity F false _ _ _
          (gateIndex_strictAnti hqq) (hcond'.2 j hij) (hcond.2 j hij))
  calc
    jointSensitivityAt (recursiveFamily T label F q) (recursiveFamily T label F q') x ≤
        (U ∪ V).card := Finset.card_le_card hsub
    _ ≤ U.card + V.card := Finset.card_union_le _ _
    _ ≤ r * sideSensitivity F true + o * jointSensitivity F false := Nat.add_le_add hU hV
    _ = _ := Nat.add_comm _ _

end Paper320

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320
open scoped Classical


end Component2

-- Source component: Theorems/Thm_OAI_Paper320_Tournament_card_internalEdges.lean
section Component3
-- Accepted Prove2Me submission 01169cff-70fc-4a9b-beeb-8fe09eaa6258
-- Local packaging: deduplicated identical-name helpers; retained their first accepted proof.
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/TournamentCounts.lean:L19-L45
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.Tournament.card_internalEdges. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.

-- ---- from OAI.Combinatorics.Sensitivity.Tournament ----
namespace OAI

/-! Finite tournaments and the target-constant labeling condition. -/

noncomputable section
open scoped Classical

namespace Paper320

namespace Tournament
variable {k : ℕ} (T : Tournament k)

theorem not_adj_reverse {i j : Fin k} (h : T.Adj i j) : ¬ T.Adj j i :=
  (T.edge_compl (T.ne_of_adj h)).mp h

theorem adj_or_reverse {i j : Fin k} (h : i ≠ j) : T.Adj i j ∨ T.Adj j i := by
  by_cases hh : T.Adj j i
  · exact Or.inr hh
  · exact Or.inl ((T.edge_compl h).mpr hh)

end Tournament

namespace GoodLabeling
variable {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)

end GoodLabeling
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.TournamentCounts ----
namespace OAI

/-! The exact internal edge count and the small gate-candidate bound. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320.Tournament
variable {k : ℕ} (T : Tournament k)

theorem card_internalEdges (I : Finset (Fin k)) :
    (T.internalEdges I).card = I.card.choose 2 := by
  let U := T.internalEdges I
  let V := (I ×ˢ I).filter fun p => T.Adj p.2 p.1
  have hd : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact T.not_adj_reverse (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
  have hu : U.disjUnion V hd = I.offDiag := by
    ext ⟨i,j⟩
    simp only [Finset.mem_disjUnion, U, V, internalEdges, Finset.mem_filter,
      Finset.mem_product, Finset.mem_offDiag]
    constructor
    · rintro (⟨⟨hi,hj⟩,h⟩ | ⟨⟨hi,hj⟩,h⟩)
      · exact ⟨hi,hj,T.ne_of_adj h⟩
      · exact ⟨hi,hj,(T.ne_of_adj h).symm⟩
    · rintro ⟨hi,hj,hne⟩
      exact (T.adj_or_reverse hne).imp (fun h => ⟨⟨hi,hj⟩,h⟩) (fun h => ⟨⟨hi,hj⟩,h⟩)
  have hs : U.card = V.card := Finset.card_equiv (Equiv.prodComm (Fin k) (Fin k)) (by
    intro p
    simp only [U,V,internalEdges,Finset.mem_filter,Finset.mem_product,Equiv.prodComm_apply]
    tauto)
  have hc := congrArg Finset.card hu
  rw [Finset.card_disjUnion, ← hs, Finset.offDiag_card] at hc
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  change U.card = _
  omega

end Paper320.Tournament

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320 OAI.Paper320.Tournament
open scoped Classical BigOperators
variable {k : ℕ} (T : Tournament k)


end Component3

-- Source component: Theorems/Thm_OAI_Paper320_Tournament_card_le_three_of_outdegree_le_one.lean
section Component4
-- Accepted Prove2Me submission 2956543b-e4d5-4b9c-90a7-e1668a39898c
-- Local packaging: deduplicated identical-name helpers; retained their first accepted proof.
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/TournamentCounts.lean:L51-L63
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.Tournament.card_le_three_of_outdegree_le_one. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.

-- ---- from OAI.Combinatorics.Sensitivity.TournamentCounts ----
namespace OAI

/-! The exact internal edge count and the small gate-candidate bound. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320.Tournament
variable {k : ℕ} (T : Tournament k)

theorem sum_outdegree_eq (I : Finset (Fin k)) :
    ∑ i ∈ I, (I.filter (T.Adj i)).card = (T.internalEdges I).card := by
  simp only [internalEdges, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

theorem card_le_three_of_outdegree_le_one (I : Finset (Fin k))
    (h : ∀ i ∈ I, (I.filter (T.Adj i)).card ≤ 1) : I.card ≤ 3 := by
  have hsum := Finset.sum_le_sum h
  have hc : I.card.choose 2 ≤ I.card := by
    rw [← T.card_internalEdges, ← T.sum_outdegree_eq]
    simpa only [Finset.sum_const_nat, mul_one] using hsum
  have hdouble : I.card * (I.card - 1) ≤ 2 * I.card + 1 := by
    rw [Nat.choose_two_right] at hc
    omega
  by_contra hn
  have h4 : 4 ≤ I.card := by omega
  have ht : I.card - 1 + 1 = I.card := by omega
  nlinarith

end Paper320.Tournament

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320 OAI.Paper320.Tournament
open scoped Classical BigOperators
variable {k : ℕ} (T : Tournament k)


end Component4

-- Source component: Theorems/Thm_OAI_Paper320_recursive_sensitivity_zero_at.lean
section Component5
-- Accepted Prove2Me submission c194c3a2-8ccf-430b-b019-178838a7f3e1
-- Local packaging: deduplicated identical-name helpers; retained their first accepted proof.
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/RecursiveZero.lean:L12-L107
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.recursive_sensitivity_zero_at. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveProfiles ----
namespace OAI

/-! The side and joint profiles count literal flips of the same raw input. -/

noncomputable section
open scoped Classical

namespace Paper320

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Tournament ----
namespace OAI

/-! Finite tournaments and the target-constant labeling condition. -/

noncomputable section
open scoped Classical

namespace Paper320

namespace Tournament
variable {k : ℕ} (T : Tournament k)

theorem internal_sink_unique {I : Finset (Fin k)} {i j : Fin k}
    (hi : i ∈ I) (hj : j ∈ I)
    (hsi : ∀ v ∈ I, ¬ T.Adj i v) (hsj : ∀ v ∈ I, ¬ T.Adj j v) : i = j := by
  by_contra h
  rcases T.adj_or_reverse h with hh | hh
  · exact hsi j hj hh
  · exact hsj i hi hh

end Tournament

namespace GoodLabeling
variable {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)

theorem good_implies_card_lt_sixteen (I : Finset (Fin k)) (m : Fin k → Fin r)
    (h : ∀ i ∈ I, ∀ j ∈ I, T.Adj i j → A.label i j = m j) : I.card < 16 := by
  by_contra hn
  obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq (show 16 ≤ I.card by omega)
  obtain ⟨i, hi, j, hj, hij, hne⟩ := A.good J hJ m
  exact hne (h i (hJI hi) j (hJI hj) hij)

end GoodLabeling
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveDefinitions ----
namespace OAI

/-! The literal target-row and labeled-gate construction. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem gateIndex_lt_last {h : ℕ} (q : Fin h) : gateIndex q < Fin.last h :=
  Fin.castSucc_lt_last _

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveSets ----
namespace OAI

/-! Finite sets of changing raw coordinates inside an individual child. -/

noncomputable section
open scoped Classical

namespace Paper320

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveFailures ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

/-! Fixed initial-input lists of clauses with exactly one failed condition. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem targetFailures_empty_iff {k r h : ℕ} {I : Type}
    (F : Fin (h + 1) → (I → Bool) → Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    targetFailures F x i = ∅ ↔ ∀ c, F (Fin.last h) (recursiveChild x i c) = true := by
  simp [targetFailures, Finset.filter_eq_empty_iff]

theorem gateFailures_empty_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    gateFailures T label F q x i = ∅ ↔
      ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false := by
  simp [gateFailures, Finset.filter_eq_empty_iff]

theorem targetFailures_singleton {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : i ∈ targetCandidates T label F q x) :
    targetFailures F x i = {targetWitness F x hr i} := by
  have hc := (Finset.mem_filter.mp hi).2.1
  obtain ⟨c, hc'⟩ := Finset.card_eq_one.mp hc
  have hne : (targetFailures F x i).Nonempty := hc' ▸ Finset.singleton_nonempty c
  have hm : targetWitness F x hr i ∈ targetFailures F x i := by
    simp only [targetWitness, dite_eq_left hne]
    exact hne.choose_spec
  rw [hc', Finset.mem_singleton] at hm
  simpa [hm] using hc'

theorem gateFailures_singleton {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ gateCandidates T label F q x) :
    gateFailures T label F q x i = {gateWitness T label F q x i} := by
  have hc := (Finset.mem_filter.mp hi).2.2
  obtain ⟨j, hc'⟩ := Finset.card_eq_one.mp hc
  have hne : (gateFailures T label F q x i).Nonempty := hc' ▸ Finset.singleton_nonempty j
  have hm : gateWitness T label F q x i ∈ gateFailures T label F q x i := by
    simp only [gateWitness, dite_eq_left hne]
    exact hne.choose_spec
  rw [hc', Finset.mem_singleton] at hm
  simpa [hm] using hc'

theorem targetCandidates_card {k r h : ℕ} {I : Type} (T : Tournament k)
    (A : GoodLabeling T r) (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    (targetCandidates T A.label F q x).card < 16 := by
  apply A.good_implies_card_lt_sixteen _ (targetWitness F x hr)
  intro i hi j hj hij
  have hgate := (gateFailures_empty_iff T A.label F q x i).mp (Finset.mem_filter.mp hi).2.2
  have hz := hF.rejects_of_le (gateIndex_lt_last q).le (hgate j hij)
  have hm : A.label i j ∈ targetFailures F x j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
  rw [targetFailures_singleton T A.label F q x hr j hj, Finset.mem_singleton] at hm
  exact hm

theorem gateCandidates_neighbor {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (hi : i ∈ gateCandidates T label F q x)
    (hj : j ∈ gateCandidates T label F q x) (hij : T.Adj i j) :
    j = gateWitness T label F q x i := by
  have ht := (targetFailures_empty_iff F x j).mp (Finset.mem_filter.mp hj).2.1
  have hon := hF.accepts_of_le (gateIndex_lt_last q).le (ht (label i j))
  have hm : j ∈ gateFailures T label F q x i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hon⟩
  rwa [gateFailures_singleton T label F q x i hi, Finset.mem_singleton] at hm

theorem gateCandidates_card {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    (gateCandidates T label F q x).card ≤ 3 := by
  apply T.card_le_three_of_outdegree_le_one
  intro i hi
  apply le_trans (Finset.card_le_card (t := {gateWitness T label F q x i}) ?_)
    (by simp)
  intro j hj
  have h := Finset.mem_filter.mp hj
  exact Finset.mem_singleton.mpr (gateCandidates_neighbor T label F hF q x i j hi h.1 h.2)

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveCandidates ----
namespace OAI

/-! Unique failed children and the unique possible sink of the gate-clause list. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem targetWitness_false {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : i ∈ targetCandidates T label F q x) :
    F (Fin.last h) (recursiveChild x i (targetWitness F x hr i)) = false := by
  have hm : targetWitness F x hr i ∈ targetFailures F x i := by
    rw [targetFailures_singleton T label F q x hr i hi]
    exact Finset.mem_singleton_self _
  exact (Finset.mem_filter.mp hm).2

theorem targetWitness_unique {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : i ∈ targetCandidates T label F q x) (c : Fin r)
    (hc : F (Fin.last h) (recursiveChild x i c) = false) : c = targetWitness F x hr i := by
  have hm : c ∈ targetFailures F x i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  rwa [targetFailures_singleton T label F q x hr i hi, Finset.mem_singleton] at hm

theorem gateWitness_spec {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ gateCandidates T label F q x) :
    T.Adj i (gateWitness T label F q x i) ∧
      F (gateIndex q) (recursiveChild x (gateWitness T label F q x i)
        (label i (gateWitness T label F q x i))) = true := by
  have hm : gateWitness T label F q x i ∈ gateFailures T label F q x i := by
    rw [gateFailures_singleton T label F q x i hi]
    exact Finset.mem_singleton_self _
  exact (Finset.mem_filter.mp hm).2

theorem gateWitness_unique {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : i ∈ gateCandidates T label F q x) (j : Fin k) (hij : T.Adj i j)
    (hj : F (gateIndex q) (recursiveChild x j (label i j)) = true) :
    j = gateWitness T label F q x i := by
  have hm : j ∈ gateFailures T label F q x i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hj⟩
  rwa [gateFailures_singleton T label F q x i hi, Finset.mem_singleton] at hm

theorem gateSinks_card {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    (gateSinks T label F q x).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact T.internal_sink_unique (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem nonsink_gateWitness_mem {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i : Fin k) (hi : i ∈ gateCandidates T label F q x)
    (hs : i ∉ gateSinks T label F q x) :
    gateWitness T label F q x i ∈ gateCandidates T label F q x := by
  have he : ∃ j ∈ gateCandidates T label F q x, T.Adj i j := by
    by_contra hn
    apply hs
    apply Finset.mem_filter.mpr
    refine ⟨hi, ?_⟩
    intro j hj hij
    exact hn ⟨j, hj, hij⟩
  obtain ⟨j, hj, hij⟩ := he
  rwa [← gateCandidates_neighbor T label F hF q x i j hi hj hij]

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveZero ----
namespace OAI

/-! The zero-side recurrence separates the unique possible gate-list sink. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursive_sensitivity_zero_at {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : GoodLabeling T r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T A.label F q x = false) :
    sensitivityAt (recursiveFamily T A.label F q) x ≤
      16 * sideSensitivity F false + sideSensitivity F true + 3 * jointSensitivity F true := by
  let TC := targetCandidates T A.label F q x
  let GC := gateCandidates T A.label F q x
  let SC := gateSinks T A.label F q x
  let NC := GC \ SC
  let w := gateWitness T A.label F q x
  let U := TC.biUnion fun i => childChanges F (Fin.last h) x i (targetWitness F x hr i)
  let V := NC.biUnion fun i => childJointChanges F (gateIndex q) (Fin.last h) x (w i) (A.label i (w i))
  let W := SC.biUnion fun i => childChanges F (gateIndex q) x (w i) (A.label i (w i))
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T A.label F q (flip x {p}) ≠ recursiveFamily T A.label F q x) ⊆ U ∪ (V ∪ W) := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    have hchange := (Finset.mem_filter.mp hp).2
    have hon : recursiveFamily T A.label F q (flip x {((j, c), a)}) = true := by
      cases hy : recursiveFamily T A.label F q (flip x {((j, c), a)})
      · exact False.elim (hchange (hy.trans hx.symm))
      · rfl
    obtain ⟨i, hi⟩ := (recursiveFamily_eq_true_iff T A.label F q _).mp hon
    have hioff := (recursiveFamily_eq_false_iff T A.label F q x).mp hx i
    rcases rowClause_repair_cases T A.label F q x i j c a hioff hi with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, hij, rfl, hgon, hgoff⟩
    · subst j
      have hc := targetWitness_unique T A.label F q x hr i hit c htoff
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hit, ?_⟩
      have hn : F (Fin.last h) (flip (recursiveChild x i c) {a}) ≠
          F (Fin.last h) (recursiveChild x i c) := by simp [hton, htoff]
      simpa [childChanges, hc] using hn
    · have hj := gateWitness_unique T A.label F q x i hig j hij hgon
      apply Finset.mem_union_right
      by_cases hs : i ∈ SC
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, hs, ?_⟩
        have hn : F (gateIndex q) (flip (recursiveChild x j (A.label i j)) {a}) ≠
            F (gateIndex q) (recursiveChild x j (A.label i j)) := by simp [hgon, hgoff]
        simpa [childChanges, w, hj] using hn
      · have hwg := nonsink_gateWitness_mem T A.label F hF q x i hig hs
        have hjg : j ∈ gateCandidates T A.label F q x := by simpa [hj] using hwg
        have hton := (targetFailures_empty_iff F x j).mp (Finset.mem_filter.mp hjg).2.1 (A.label i j)
        have htoff := hF.rejects_of_le (gateIndex_lt_last q).le hgoff
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_sdiff.mpr ⟨hig, hs⟩, ?_⟩
        have hn :
            F (gateIndex q) (flip (recursiveChild x j (A.label i j)) {a}) ≠
              F (gateIndex q) (recursiveChild x j (A.label i j)) ∧
            F (Fin.last h) (flip (recursiveChild x j (A.label i j)) {a}) ≠
              F (Fin.last h) (recursiveChild x j (A.label i j)) := by
          simp [hgon, hgoff, hton, htoff]
        simpa [childJointChanges, w, hj] using hn
  have hU : U.card ≤ 16 * sideSensitivity F false := by
    calc
      U.card ≤ TC.card * sideSensitivity F false :=
        card_biUnion_le_mul TC _ _ (fun i hi => by
          rw [childChanges_card]
          exact sensitivityAt_le_sideSensitivity F false _ _
            (targetWitness_false T A.label F q x hr i hi))
      _ ≤ 16 * sideSensitivity F false := Nat.mul_le_mul_right _
        (Nat.le_of_lt (targetCandidates_card T A F hF q x hr))
  have hV : V.card ≤ 3 * jointSensitivity F true := by
    calc
      V.card ≤ NC.card * jointSensitivity F true :=
        card_biUnion_le_mul NC _ _ (fun i hi => by
          have hg := Finset.mem_sdiff.mp hi
          have hw := nonsink_gateWitness_mem T A.label F hF q x i hg.1 hg.2
          have hgate := (gateWitness_spec T A.label F q x i hg.1).2
          have htarget := (targetFailures_empty_iff F x _).mp (Finset.mem_filter.mp hw).2.1
            (A.label i (w i))
          rw [childJointChanges_card]
          exact jointSensitivityAt_le_jointSensitivity F true _ _ _ (gateIndex_lt_last q) hgate htarget)
      _ ≤ GC.card * jointSensitivity F true := Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset)
      _ ≤ 3 * jointSensitivity F true := Nat.mul_le_mul_right _ (gateCandidates_card T A.label F hF q x)
  have hW : W.card ≤ sideSensitivity F true := by
    calc
      W.card ≤ SC.card * sideSensitivity F true :=
        card_biUnion_le_mul SC _ _ (fun i hi => by
          rw [childChanges_card]
          exact sensitivityAt_le_sideSensitivity F true _ _
            (gateWitness_spec T A.label F q x i (Finset.mem_filter.mp hi).1).2)
      _ ≤ 1 * sideSensitivity F true := Nat.mul_le_mul_right _ (gateSinks_card T A.label F q x)
      _ = _ := Nat.one_mul _
  calc
    sensitivityAt (recursiveFamily T A.label F q) x ≤ (U ∪ (V ∪ W)).card := Finset.card_le_card hsub
    _ ≤ U.card + (V ∪ W).card := Finset.card_union_le _ _
    _ ≤ U.card + (V.card + W.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ 16 * sideSensitivity F false + (3 * jointSensitivity F true + sideSensitivity F true) :=
      Nat.add_le_add hU (Nat.add_le_add hV hW)
    _ = _ := by omega

end Paper320

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320
open scoped Classical


end Component5

-- Source component: Theorems/Thm_OAI_Paper320_towerFamily_blocks.lean
section Component6
-- Accepted Prove2Me submission 8eb2023e-f6a0-4ca2-8bee-2aa9493bc714
-- Local packaging: deduplicated identical-name helpers; retained their first accepted proof.
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/Tower.lean:L133-L155
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.towerFamily_blocks. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.

-- ---- from OAI.Combinatorics.Sensitivity.Tournament ----
namespace OAI

/-! Finite tournaments and the target-constant labeling condition. -/

noncomputable section
open scoped Classical

namespace Paper320

namespace Tournament
variable {k : ℕ} (T : Tournament k)

end Tournament

namespace GoodLabeling
variable {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)

end GoodLabeling
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveDefinitions ----
namespace OAI

/-! The literal target-row and labeled-gate construction. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursiveFamily_zero {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hr : 0 < r) (hzero : ∀ q, F q (fun _ => false) = false) (q : Fin h) :
    recursiveFamily T label F q (fun _ => false) = false := by
  rw [recursiveFamily_eq_false_iff]
  intro i
  cases hi : rowClause T label F q (fun _ => false) i
  · rfl
  · have ht := ((rowClause_eq_true_iff T label F q (fun _ => false) i).mp hi).1
      (⟨0, hr⟩ : Fin r)
    have hz := hzero (Fin.last h)
    change F (Fin.last h) (fun _ => false) = true at ht
    simp [hz] at ht

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveBlocks ----
namespace OAI

/-! Disjoint zero-input blocks lift to every column of a chosen row. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursiveChild_rowLift_same {k r : ℕ} {I : Type}
    (i : Fin k) (B : Finset I) (c : Fin r) :
    recursiveChild (flip (fun _ => false) (rowLift (r := r) i B)) i c =
      flip (fun _ => false) B := by
  funext a
  simp [recursiveChild, flip]

theorem recursiveChild_rowLift_other {k r : ℕ} {I : Type}
    (i j : Fin k) (B : Finset I) (c : Fin r) (hji : j ≠ i) :
    recursiveChild (flip (fun _ => false) (rowLift (r := r) i B)) j c =
      fun _ => false := by
  funext a
  simp [recursiveChild, flip, hji]

theorem recursiveFamily_rowLift {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hzero : ∀ q, F q (fun _ => false) = false) (B : Finset I)
    (hB : ∀ q, F q (flip (fun _ => false) B) = true) (i : Fin k) (q : Fin h) :
    recursiveFamily T label F q (flip (fun _ => false) (rowLift i B)) = true := by
  apply (recursiveFamily_eq_true_iff _ _ _ _ _).mpr
  refine ⟨i, (rowClause_eq_true_iff _ _ _ _ _ _).mpr ⟨?_, ?_⟩⟩
  · intro c
    rw [recursiveChild_rowLift_same]
    exact hB _
  · intro j hij
    rw [recursiveChild_rowLift_other _ _ _ _ (T.ne_of_adj hij).symm]
    exact hzero _

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Tower ----
namespace OAI

/-! An indexed tower of the literal recursive construction and its common blocks. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem towerFamily_zero {k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (hr : 0 < r) (n h : ℕ) (hbase : ∀ q, base (h + n) q (fun _ => false) = false) :
    ∀ q, towerFamily T label base n h q (fun _ => false) = false := by
  induction n generalizing h with
  | zero =>
    change ∀ q, base h q (fun _ => false) = false
    simpa only [Nat.add_zero] using hbase
  | succ n ih =>
    apply recursiveFamily_zero T label _ hr
    apply ih
    have he : (h + 1) + n = h + (n + 1) := by omega
    rw [he]
    exact hbase

theorem towerFamily_blocks {k r : ℕ} {I K : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (blocks : K → Finset I) (hr : 0 < r) (n h : ℕ)
    (hzero : ∀ q, base (h + n) q (fun _ => false) = false)
    (hblocks : ∀ b q, base (h + n) q (flip (fun _ => false) (blocks b)) = true) :
    ∀ b q, towerFamily T label base n h q
      (flip (fun _ => false) (towerBlocks blocks n b)) = true := by
  induction n generalizing h with
  | zero =>
    change ∀ b q, base h q (flip (fun _ => false) (blocks b)) = true
    simpa only [Nat.add_zero] using hblocks
  | succ n ih =>
    intro b q
    have he : (h + 1) + n = h + (n + 1) := by omega
    have hz : ∀ q, base ((h + 1) + n) q (fun _ => false) = false := by
      rw [he]
      exact hzero
    have hb : ∀ b q, base ((h + 1) + n) q (flip (fun _ => false) (blocks b)) = true := by
      rw [he]
      exact hblocks
    exact recursiveFamily_rowLift T label _
      (towerFamily_zero T label base hr n (h + 1) hz)
      (towerBlocks blocks n b.2) (ih (h + 1) hz hb b.2) b.1 q

end Paper320

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320
open scoped Classical


end Component6

-- Source component: Theorems/Thm_OAI_Paper320_Tournament_labelingConstraint_iff.lean
section Component7
-- Accepted Prove2Me submission e83b9bd9-ac6b-46af-98e7-f84356fafff0
-- Local packaging: deduplicated identical-name helpers; retained their first accepted proof.
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/LabelingConstraints.lean:L17-L35
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.Tournament.labelingConstraint_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.

-- ---- from OAI.Combinatorics.Sensitivity.LabelingConstraints ----
namespace OAI

/-! The labeling constraints are exactly fixed values on the internal edges. -/

noncomputable section
open scoped Classical

namespace Paper320.Tournament
variable {k : ℕ} (T : Tournament k)

theorem mem_internalEdges {I : Finset (Fin k)} {p : Fin k × Fin k} :
    p ∈ T.internalEdges I ↔ (p.1 ∈ I ∧ p.2 ∈ I) ∧ T.Adj p.1 p.2 := by
  simp only [internalEdges, Finset.mem_filter, Finset.mem_product]

theorem labelingConstraint_iff {α β : Type} [Nonempty α]
    (s : Finset α) (v : α → Fin k) (m : α → β) (hv : Function.Injective v)
    (A : (Fin k × Fin k) → β) :
    (∀ i ∈ s, ∀ j ∈ s, T.Adj (v i) (v j) → A (v i,v j) = m j) ↔
      ∀ p ∈ T.internalEdges (s.image v), A p = m (Function.invFun v p.2) := by
  constructor
  · intro h p hp
    obtain ⟨⟨hp₁,hp₂⟩,ha⟩ := T.mem_internalEdges.mp hp
    obtain ⟨i,hi,hvi⟩ := Finset.mem_image.mp hp₁
    obtain ⟨j,hj,hvj⟩ := Finset.mem_image.mp hp₂
    have he : p = (v i,v j) := Prod.ext hvi.symm hvj.symm
    subst p
    rw [Function.leftInverse_invFun hv j]
    exact h i hi j hj ha
  · intro h i hi j hj ha
    have hp : (v i,v j) ∈ T.internalEdges (s.image v) :=
      T.mem_internalEdges.mpr ⟨⟨Finset.mem_image.mpr ⟨i,hi,rfl⟩,
        Finset.mem_image.mpr ⟨j,hj,rfl⟩⟩,ha⟩
    simpa only [Function.leftInverse_invFun hv j] using h (v i,v j) hp

end Paper320.Tournament

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320 OAI.Paper320.Tournament
open scoped Classical
variable {k : ℕ} (T : Tournament k)


end Component7

-- Source component: Theorems/Thm_OAI_Paper320_Tournament_card_badLabelings_le.lean
section Component8
-- Accepted Prove2Me submission 18a859cb-6a27-4582-a2bb-92efb631a9ff
-- Local packaging: deduplicated identical-name helpers; retained their first accepted proof.
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/LabelingEvents.lean:L69-L81
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.Tournament.card_badLabelings_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.

-- ---- from OAI.Combinatorics.Sensitivity.FixedCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Exact finite counting when a specified set of coordinates is fixed. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]

theorem card_fixedCoordinates (s : Finset α) (v : α → β)
    [DecidablePred (fun f : α → β => ∀ i ∈ s, f i = v i)] :
    (Finset.univ.filter fun f : α → β => ∀ i ∈ s, f i = v i).card =
      Fintype.card β ^ (Fintype.card α - s.card) := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (fixedCoordinatesEquiv s v), Fintype.card_fun,
    Fintype.card_subtype_compl, Fintype.card_coe]

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.LabelingEvents ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Exact counts of target-constant label constraints on sixteen vertices. -/

noncomputable section
open scoped Classical BigOperators

namespace Paper320.Tournament
variable {k r n : ℕ} (T : Tournament k)

theorem labelingEvent_eq [NeZero n] (v : Fin n → Fin k) (m : Fin n → Fin r)
    (hv : Function.Injective v) :
    T.labelingEvent v m = Finset.univ.filter fun A =>
      ∀ p ∈ T.internalEdges (Finset.univ.image v), A p = m (Function.invFun v p.2) := by
  rw [labelingEvent, ite_eq_left hv]
  apply Finset.filter_congr
  intro A _
  simpa only [Finset.mem_univ, forall_const] using
    T.labelingConstraint_iff Finset.univ v m hv A

theorem card_labelingEvent [NeZero n] (v : Fin n → Fin k) (m : Fin n → Fin r)
    (hv : Function.Injective v) :
    (T.labelingEvent v m).card = r ^ (k*k-n.choose 2) := by
  rw [T.labelingEvent_eq v m hv]
  have hc := card_fixedCoordinates (T.internalEdges (Finset.univ.image v))
    (fun p => m (Function.invFun v p.2))
  rw [T.card_internalEdges] at hc
  have hi : (Finset.univ.image v).card = n := by
    rw [Finset.card_image_of_injective _ hv]
    exact Fintype.card_fin n
  rw [hi] at hc
  simpa only [Fintype.card_fin, Fintype.card_prod] using hc

theorem card_labelingEvent_le [NeZero n] (v : Fin n → Fin k) (m : Fin n → Fin r) :
    (T.labelingEvent v m).card ≤ r ^ (k*k-n.choose 2) := by
  by_cases hv : Function.Injective v
  · exact (T.card_labelingEvent v m hv).le
  · simp only [labelingEvent, ite_eq_right hv, Finset.card_empty, Nat.zero_le]

theorem card_badLabelings_le [NeZero n] :
    (T.badLabelings n r).card ≤ k^n * r^n * r^(k*k-n.choose 2) := by
  calc
    (T.badLabelings n r).card ≤ ∑ v : Fin n → Fin k,
        (Finset.univ.biUnion fun m : Fin n → Fin r => T.labelingEvent v m).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v : Fin n → Fin k, ∑ _m : Fin n → Fin r, r^(k*k-n.choose 2) := by
      apply Finset.sum_le_sum
      intro v _
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun m _ =>
        T.card_labelingEvent_le v m)
    _ = k^n * r^n * r^(k*k-n.choose 2) := by
      simp [Nat.mul_assoc]

end Paper320.Tournament

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320 OAI.Paper320.Tournament
open scoped Classical BigOperators
variable {k r n : ℕ} (T : Tournament k)


end Component8

-- Source component: Solutions/Transfer.lean
section Component9

open OAI.Paper320
open scoped Classical

namespace Sensitivity205
noncomputable section

structure Labeling {k : ℕ} (T : Tournament k) (r t : ℕ) where
  label : Fin k → Fin k → Fin r
  coherent_card : ∀ (I : Finset (Fin k)) (m : Fin k → Fin r),
    (∀ i ∈ I, ∀ j ∈ I, T.Adj i j → label i j = m j) → I.card < t

theorem labeling_exists {k r t : ℕ} [NeZero t] (T : Tournament k)
    (hr : 0 < r) (ht : t.choose 2 ≤ k*k)
    (hp : k^t * r^t < r^(t.choose 2)) : Nonempty (Labeling T r t) := by
  have htotal : k^t*r^t*r^(k*k-t.choose 2) < r^(k*k) := by
    calc
      _ < r^(t.choose 2)*r^(k*k-t.choose 2) :=
        Nat.mul_lt_mul_of_pos_right hp (pow_pos hr _)
      _ = r^(k*k) := by rw [← pow_add, Nat.add_sub_of_le ht]
  have hc : (T.badLabelings t r).card <
      (Finset.univ : Finset ((Fin k × Fin k) → Fin r)).card := by
    simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
      using (T.card_badLabelings_le (r := r) (n := t)).trans_lt htotal
  obtain ⟨A, _, hA⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨⟨fun i j => A (i,j), ?_⟩⟩
  intro I m hcoh
  by_contra hn
  obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hn)
  let e : Fin t ≃ J := (Finset.equivFinOfCardEq hJ).symm
  let v : Fin t → Fin k := fun i => (e i).val
  have hv : Function.Injective v := Subtype.val_injective.comp e.injective
  apply hA
  apply Finset.mem_biUnion.mpr
  refine ⟨v, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨fun i => m (v i),
    Finset.mem_univ _, ?_⟩⟩
  simp only [Tournament.labelingEvent, if_pos hv, Finset.mem_filter,
    Finset.mem_univ, true_and]
  intro i j hij
  exact hcoh (v i) (hJI (e i).property) (v j) (hJI (e j).property) hij

theorem targetCandidates_card {k r h t : ℕ} {I : Type}
    (T : Tournament k) (A : Labeling T r t)
    (F : Fin (h+1) → (I → Bool) → Bool) (hF : NestedFamily F)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) :
    (targetCandidates T A.label F q x).card < t := by
  apply A.coherent_card _ (targetWitness F x hr)
  intro i hi j hj hij
  have hgate := (gateFailures_empty_iff T A.label F q x i).mp
    (Finset.mem_filter.mp hi).2.2 j hij
  have htarget := hF.rejects_of_le (gateIndex_lt_last q).le hgate
  exact targetWitness_unique T A.label F q x hr j hj (A.label i j) htarget

def PairBound {n : ℕ} {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (b : Bool) (V : Fin n → Fin n → ℕ) : Prop :=
  ∀ (q q' : Fin n), q ≤ q' → ∀ x, F q x = b → F q' x = b →
    jointSensitivityAt (F q) (F q') x ≤ V q q'

@[simp] theorem joint_self {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) :
    jointSensitivityAt f f x = sensitivityAt f x := by
  simp [jointSensitivityAt, sensitivityAt]

theorem PairBound.self {n : ℕ} {I : Type} [Fintype I]
    {F : Fin n → (I → Bool) → Bool} {b : Bool} {V : Fin n → Fin n → ℕ}
    (hV : PairBound F b V) (q : Fin n) (x : I → Bool) (hx : F q x = b) :
    sensitivityAt (F q) x ≤ V q q := by
  simpa using hV q q le_rfl x hx hx

theorem recursive_pair_zero {k r h t : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (A : Labeling T r t)
    (F : Fin (h+1) → (I → Bool) → Bool) (hF : NestedFamily F) (hr : 0 < r)
    (Z Y : Fin (h+1) → Fin (h+1) → ℕ)
    (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (q q' : Fin h) (hqq : q ≤ q')
    (hYC : Y (gateIndex q') (Fin.last h) ≤ Y (gateIndex q') (gateIndex q))
    (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T A.label F q x = false)
    (hx' : recursiveFamily T A.label F q' x = false) :
    jointSensitivityAt (recursiveFamily T A.label F q) (recursiveFamily T A.label F q') x ≤
      (t-1) * Z (Fin.last h) (Fin.last h) +
        Y (gateIndex q') (gateIndex q) + 2 * Y (gateIndex q') (Fin.last h) := by
  let TC := targetCandidates T A.label F q x
  let GC := gateCandidates T A.label F q x
  let SC := gateSinks T A.label F q x
  let NC := GC \ SC
  let w := gateWitness T A.label F q x
  let U := TC.biUnion fun i => childChanges F (Fin.last h) x i (targetWitness F x hr i)
  let V := NC.biUnion fun i => childJointChanges F (gateIndex q') (Fin.last h) x (w i) (A.label i (w i))
  let W := SC.biUnion fun i => childJointChanges F (gateIndex q') (gateIndex q) x (w i) (A.label i (w i))
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T A.label F q (flip x {p}) ≠ recursiveFamily T A.label F q x ∧
      recursiveFamily T A.label F q' (flip x {p}) ≠ recursiveFamily T A.label F q' x) ⊆ U ∪ (V ∪ W) := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    have hchange := (Finset.mem_filter.mp hp).2
    have hon' : recursiveFamily T A.label F q' (flip x {((j,c),a)}) = true := by
      cases hy : recursiveFamily T A.label F q' (flip x {((j,c),a)})
      · exact False.elim (hchange.2 (hy.trans hx'.symm))
      · rfl
    obtain ⟨i, hi'⟩ := (recursiveFamily_eq_true_iff T A.label F q' _).mp hon'
    have hi := rowClause_nested T A.label F hF hqq _ i hi'
    have hioff := (recursiveFamily_eq_false_iff T A.label F q x).mp hx i
    rcases rowClause_repair_cases T A.label F q x i j c a hioff hi with
      ⟨hit, hji, htoff, hton⟩ | ⟨hig, hij, rfl, hgon, hgoff⟩
    · subst j
      have hc := targetWitness_unique T A.label F q x hr i hit c htoff
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hit, ?_⟩
      have hn : F (Fin.last h) (flip (recursiveChild x i c) {a}) ≠
          F (Fin.last h) (recursiveChild x i c) := by simp [hton, htoff]
      simpa [childChanges, hc] using hn
    · have hj := gateWitness_unique T A.label F q x i hig j hij hgon
      have hgon' := hF.accepts_of_le (gateIndex_antitone hqq) hgon
      have hgoff' := ((rowClause_eq_true_iff T A.label F q' _ i).mp hi').2 j hij
      rw [recursiveChild_flip_same] at hgoff'
      apply Finset.mem_union_right
      by_cases hs : i ∈ SC
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, hs, ?_⟩
        have hn :
            F (gateIndex q') (flip (recursiveChild x j (A.label i j)) {a}) ≠
              F (gateIndex q') (recursiveChild x j (A.label i j)) ∧
            F (gateIndex q) (flip (recursiveChild x j (A.label i j)) {a}) ≠
              F (gateIndex q) (recursiveChild x j (A.label i j)) := by
          simp [hgon, hgoff, hgon', hgoff']
        simpa [childJointChanges, w, hj] using hn
      · have hwg := nonsink_gateWitness_mem T A.label F hF q x i hig hs
        have hjg : j ∈ gateCandidates T A.label F q x := by simpa [hj] using hwg
        have hton := (targetFailures_empty_iff F x j).mp (Finset.mem_filter.mp hjg).2.1 (A.label i j)
        have htoff := hF.rejects_of_le (gateIndex_lt_last q').le hgoff'
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_sdiff.mpr ⟨hig, hs⟩, ?_⟩
        have hn :
            F (gateIndex q') (flip (recursiveChild x j (A.label i j)) {a}) ≠
              F (gateIndex q') (recursiveChild x j (A.label i j)) ∧
            F (Fin.last h) (flip (recursiveChild x j (A.label i j)) {a}) ≠
              F (Fin.last h) (recursiveChild x j (A.label i j)) := by
          simp [hgon', hgoff', hton, htoff]
        simpa [childJointChanges, w, hj] using hn
  have hU : U.card ≤ (t-1) * Z (Fin.last h) (Fin.last h) := by
    calc
      U.card ≤ TC.card * Z (Fin.last h) (Fin.last h) :=
        card_biUnion_le_mul TC _ _ (fun i hi => by
          rw [childChanges_card]
          exact hZ.self _ _ (targetWitness_false T A.label F q x hr i hi))
      _ ≤ _ := Nat.mul_le_mul_right _ (by
        have hc := targetCandidates_card T A F hF q x hr
        dsimp only [TC]; omega)
  have hV : V.card ≤ NC.card * Y (gateIndex q') (Fin.last h) := by
    apply card_biUnion_le_mul
    intro i hi
    have hg := Finset.mem_sdiff.mp hi
    have hw := nonsink_gateWitness_mem T A.label F hF q x i hg.1 hg.2
    have hgate := (gateWitness_spec T A.label F q x i hg.1).2
    have htarget := (targetFailures_empty_iff F x _).mp (Finset.mem_filter.mp hw).2.1 (A.label i (w i))
    rw [childJointChanges_card]
    exact hY _ _ (gateIndex_lt_last q').le _
      (hF.accepts_of_le (gateIndex_antitone hqq) hgate) htarget
  have hW : W.card ≤ SC.card * Y (gateIndex q') (gateIndex q) := by
    apply card_biUnion_le_mul
    intro i hi
    have hg := (gateWitness_spec T A.label F q x i (Finset.mem_filter.mp hi).1).2
    rw [childJointChanges_card]
    exact hY _ _ (gateIndex_antitone hqq) _
      (hF.accepts_of_le (gateIndex_antitone hqq) hg) hg
  have hVW : V.card + W.card ≤ Y (gateIndex q') (gateIndex q) +
      2 * Y (gateIndex q') (Fin.last h) := by
    have hgc : GC.card ≤ 3 := gateCandidates_card T A.label F hF q x
    have hsc : SC.card ≤ 1 := gateSinks_card T A.label F q x
    by_cases hSC : SC.Nonempty
    · have hcs : SC ⊆ GC := Finset.filter_subset _ _
      have hc : NC.card + SC.card = GC.card := Finset.card_sdiff_add_card_eq_card hcs
      have hpos := Finset.card_pos.mpr hSC
      have hn : NC.card ≤ 2 := by omega
      have hv := hV.trans (Nat.mul_le_mul_right _ hn)
      have hw := hW.trans (Nat.mul_le_mul_right _ hsc)
      omega
    · have hSC0 : SC = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSC
      have hw : W = ∅ := by simp only [W, hSC0, Finset.biUnion_empty]
      have hn : NC.card ≤ 3 := (Finset.card_le_card Finset.sdiff_subset).trans hgc
      have hv := hV.trans (Nat.mul_le_mul_right _ hn)
      simp only [hw, Finset.card_empty] at *
      omega
  calc
    jointSensitivityAt _ _ x ≤ (U ∪ (V ∪ W)).card := Finset.card_le_card hsub
    _ ≤ U.card + (V ∪ W).card := Finset.card_union_le _ _
    _ ≤ U.card + (V.card + W.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ _ := by have := Nat.add_le_add hU hVW; omega

theorem recursive_pair_one {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o)
    (Z Y : Fin (h+1) → Fin (h+1) → ℕ)
    (hZ : PairBound F false Z) (hY : PairBound F true Y)
    (q q' : Fin h) (hqq : q ≤ q') (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T label F q x = true)
    (hx' : recursiveFamily T label F q' x = true) :
    jointSensitivityAt (recursiveFamily T label F q) (recursiveFamily T label F q') x ≤
      o * Z (gateIndex q') (gateIndex q) + r * Y (Fin.last h) (Fin.last h) := by
  obtain ⟨i, hi'⟩ := (recursiveFamily_eq_true_iff T label F q' x).mp hx'
  have hi := rowClause_nested T label F hF hqq x i hi'
  have hcond := (rowClause_eq_true_iff T label F q x i).mp hi
  have hcond' := (rowClause_eq_true_iff T label F q' x i).mp hi'
  let U := Finset.univ.biUnion fun c => childChanges F (Fin.last h) x i c
  let V := (Finset.univ.filter (T.Adj i)).biUnion fun j =>
    childJointChanges F (gateIndex q') (gateIndex q) x j (label i j)
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T label F q (flip x {p}) ≠ recursiveFamily T label F q x ∧
      recursiveFamily T label F q' (flip x {p}) ≠ recursiveFamily T label F q' x) ⊆ U ∪ V := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    have hchange := (Finset.mem_filter.mp hp).2
    have hf : recursiveFamily T label F q (flip x {((j, c), a)}) = false := by
      cases hy : recursiveFamily T label F q (flip x {((j, c), a)})
      · rfl
      · exact False.elim (hchange.1 (hy.trans hx.symm))
    have hf' : recursiveFamily T label F q' (flip x {((j, c), a)}) = false := by
      cases hy : recursiveFamily T label F q' (flip x {((j, c), a)})
      · rfl
      · exact False.elim (hchange.2 (hy.trans hx'.symm))
    have hif := (recursiveFamily_eq_false_iff T label F q _).mp hf i
    have hif' := (recursiveFamily_eq_false_iff T label F q' _).mp hf' i
    have hic : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i := by
      simp [hi, hif]
    have hic' : rowClause T label F q' (flip x {((j, c), a)}) i ≠ rowClause T label F q' x i := by
      simp [hi', hif']
    rcases rowClause_joint_flip_change T label F q q' x i j c a hic hic' with
      ⟨rfl, ht⟩ | ⟨hij, rfl, hg, hg'⟩
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨c, Finset.mem_univ _, by simpa [childChanges] using ht⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
        by simpa [childJointChanges] using And.intro hg' hg⟩
  have hU : U.card ≤ r * Y (Fin.last h) (Fin.last h) := by
    simpa [U] using card_biUnion_le_mul Finset.univ
      (fun c => childChanges F (Fin.last h) x i c) (Y (Fin.last h) (Fin.last h))
      (fun c _ => by
        rw [childChanges_card]
        exact hY.self _ _ (hcond.1 c))
  have hV : V.card ≤ o * Z (gateIndex q') (gateIndex q) := by
    simpa only [V, ho i] using card_biUnion_le_mul (Finset.univ.filter (T.Adj i))
      (fun j => childJointChanges F (gateIndex q') (gateIndex q) x j (label i j))
      (Z (gateIndex q') (gateIndex q)) (fun j hj => by
        have hij := (Finset.mem_filter.mp hj).2
        rw [childJointChanges_card]
        exact hZ _ _ (gateIndex_antitone hqq) _ (hcond'.2 j hij) (hcond.2 j hij))
  calc
    jointSensitivityAt (recursiveFamily T label F q) (recursiveFamily T label F q') x ≤
        (U ∪ V).card := Finset.card_le_card hsub
    _ ≤ U.card + V.card := Finset.card_union_le _ _
    _ ≤ r * Y (Fin.last h) (Fin.last h) + o * Z (gateIndex q') (gateIndex q) := Nat.add_le_add hU hV
    _ = _ := Nat.add_comm _ _

end
end Sensitivity205

end Component9

-- Source component: Solutions/Base.lean
section Component10

open OAI.Paper320
open scoped Classical BigOperators

namespace Sensitivity205
noncomputable section

def threshold (q : Fin 3) (x : Fin 3 → Bool) : Bool :=
  decide (q.val + 1 ≤ (Finset.univ.filter fun i => x i = true).card)

theorem threshold_nested : NestedFamily threshold := by
  constructor
  intro q q' x hqq hx
  simp only [threshold, decide_eq_true_eq] at *
  exact le_trans (Nat.add_le_add_right hqq 1) hx

def flip3 (x : Fin 3 → Bool) (i : Fin 3) : Fin 3 → Bool :=
  fun j => if j = i then !(x j) else x j

theorem flip_eq3 (x : Fin 3 → Bool) (i : Fin 3) : OAI.Paper320.flip x {i} = flip3 x i := by
  funext j
  simp [OAI.Paper320.flip, flip3]

theorem sensitivityAt_threshold (q : Fin 3) (x : Fin 3 → Bool) :
    sensitivityAt (threshold q) x =
      (Finset.univ.filter fun i => threshold q (flip3 x i) ≠ threshold q x).card := by
  unfold sensitivityAt
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [flip_eq3]

theorem threshold_side_table :
    ∀ (q : Fin 3) (x : Fin 3 → Bool) (b : Bool), threshold q x = b →
      sensitivityAt (threshold q) x ≤ (if b then q.val+1 else 3-q.val) ∧
      ∀ i, threshold q (flip x {i}) ≠ threshold q x → x i = b := by
  simp_rw [sensitivityAt_threshold, flip_eq3]
  decide

theorem threshold_joint_table :
    ∀ (q q' : Fin 3) (x : Fin 3 → Bool) (b : Bool), q < q' →
      threshold q x = b → threshold q' x = b →
      ∀ i, ¬ (threshold q (flip x {i}) ≠ threshold q x ∧
        threshold q' (flip x {i}) ≠ threshold q' x) := by
  simp_rw [flip_eq3]
  decide

def base {I : Type} (g : (I → Bool) → Bool) (q : Fin 3) :
    (Fin 3 × I → Bool) → Bool := compose (threshold q) g

def Z0 (q q' : Fin 3) : ℕ := if q = q' then 3-q.val else 0
def Y0 (q q' : Fin 3) : ℕ := if q = q' then (q.val+1)*4800 else 0

theorem base_nested {I : Type} (g : (I → Bool) → Bool) : NestedFamily (base g) := by
  constructor
  intro q q' x hqq hx
  exact threshold_nested.accepts_of_le hqq hx

theorem base_side {I : Type} [Fintype I] (g : (I → Bool) → Bool)
    (b : Bool) (u : ℕ) (hg : ∀ x, g x = b → sensitivityAt g x ≤ u)
    (q : Fin 3) (x : Fin 3 × I → Bool) (hx : base g q x = b) :
    sensitivityAt (base g q) x ≤ (if b then q.val+1 else 3-q.val)*u := by
  let y : Fin 3 → Bool := fun i => g (fun a => x (i,a))
  have hy : threshold q y = b := hx
  obtain ⟨hcard, hvalue⟩ := threshold_side_table q y b hy
  rw [base, sensitivityAt_compose]
  calc
    _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => threshold q (flip y {i}) ≠ threshold q y), u := by
      apply Finset.sum_le_sum
      intro i hi
      exact hg _ (hvalue i (Finset.mem_filter.mp hi).2)
    _ = sensitivityAt (threshold q) y * u := by simp [sensitivityAt]
    _ ≤ _ := Nat.mul_le_mul_right u hcard

theorem base_joint_zero {I : Type} [Fintype I] (g : (I → Bool) → Bool)
    (q q' : Fin 3) (hqq : q < q') (x : Fin 3 × I → Bool) (b : Bool)
    (hx : base g q x = b) (hx' : base g q' x = b) :
    jointSensitivityAt (base g q) (base g q') x = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨i,a⟩ hi
  have hchange := (Finset.mem_filter.mp hi).2
  have h₁ := (compose_flip_sensitive_iff (threshold q) g x i a).mp hchange.1
  have h₂ := (compose_flip_sensitive_iff (threshold q') g x i a).mp hchange.2
  exact threshold_joint_table q q' (fun i => g (fun a => x (i,a))) b hqq hx hx' i ⟨h₁.2,h₂.2⟩

theorem base_bounds {I : Type} [Fintype I] (g : (I → Bool) → Bool) (u : ℕ)
    (h0 : ∀ x, g x = false → sensitivityAt g x ≤ u)
    (h1 : ∀ x, g x = true → sensitivityAt g x ≤ 4800*u) :
    PairBound (base g) false (fun q q' => Z0 q q'*u) ∧
    PairBound (base g) true (fun q q' => Y0 q q'*u) := by
  constructor
  · intro q q' hqq x hx hx'
    rcases eq_or_lt_of_le hqq with rfl | hlt
    · simpa [Z0] using base_side g false u h0 q x hx
    · rw [base_joint_zero g q q' hlt x false hx hx']; exact Nat.zero_le _
  · intro q q' hqq x hx hx'
    rcases eq_or_lt_of_le hqq with rfl | hlt
    · simpa [Y0, Nat.mul_assoc] using base_side g true (4800*u) h1 q x hx
    · rw [base_joint_zero g q q' hlt x true hx hx']; exact Nat.zero_le _

end
end Sensitivity205

end Component10

-- Source component: Solutions/Construction.lean
section Component11

open OAI.Paper320
open scoped Classical

namespace Sensitivity205
noncomputable section

abbrev K : ℕ := 67108865
abbrev H : ℕ := 33554432
abbrev L : ℕ := 3330000000000000000000000000000
abbrev B : ℕ := K^8

def tournament : Tournament K := cyclicTournament H

set_option maxRecDepth 10000 in
theorem labeling_nonempty : Nonempty (Labeling tournament 2 56) := by
  apply labeling_exists
  · norm_num
  · norm_num [K, Nat.choose]
  · change K^56 * 2^56 < 2^1540
    decide

def labeling : Labeling tournament 2 56 := Classical.choice labeling_nonempty

def clip (i : Fin 4) : Fin 3 := ⟨min i.val 2, by omega⟩

theorem clip_mono : Monotone clip := by
  intro i j hij
  change min i.val 2 ≤ min j.val 2
  exact min_le_min_right 2 hij

@[simp] theorem clip_gate (q : Fin 3) : clip (gateIndex q) = Fin.rev q := by
  fin_cases q <;> rfl

@[simp] theorem clip_last : clip (Fin.last 3) = 2 := rfl
@[simp] theorem clip_three : clip 3 = 2 := rfl

def extend {I : Type} (F : Fin 3 → (I → Bool) → Bool) (q : Fin 4) := F (clip q)

theorem extend_nested {I : Type} {F : Fin 3 → (I → Bool) → Bool}
    (hF : NestedFamily F) : NestedFamily (extend F) := by
  constructor
  intro q q' x hqq hx
  exact hF.accepts_of_le (clip_mono hqq) hx

def step {I : Type} (F : Fin 3 → (I → Bool) → Bool) :
    Fin 3 → ((Fin K × Fin 2) × I → Bool) → Bool :=
  recursiveFamily tournament labeling.label (extend F)

theorem step_nested {I : Type} {F : Fin 3 → (I → Bool) → Bool}
    (hF : NestedFamily F) : NestedFamily (step F) := by
  constructor
  intro q q' x hqq hx
  obtain ⟨i, hi⟩ := (recursiveFamily_eq_true_iff _ _ _ _ _).mp hx
  apply (recursiveFamily_eq_true_iff _ _ _ _ _).mpr
  exact ⟨i, rowClause_nested _ _ _ (extend_nested hF) hqq x i hi⟩

def profiles : ℕ → (Fin 3 → Fin 3 → ℕ) × (Fin 3 → Fin 3 → ℕ)
  | 0 => (Z0, Y0)
  | d+1 =>
    let (z,y) := profiles d
    (fun i j => 55*z 2 2 + y (Fin.rev j) (Fin.rev i) + 2*y (Fin.rev j) 2,
     fun i j => H*z (Fin.rev j) (Fin.rev i) + 2*y 2 2)

theorem profiles_order (d : ℕ) (hd : d ≤ 7) (i j : Fin 3) (hij : i ≤ j) :
    (profiles d).2 i 2 ≤ (profiles d).2 i j := by
  have htable : ∀ (e : Fin 8) (i j : Fin 3), i ≤ j →
      (profiles e.val).2 i 2 ≤ (profiles e.val).2 i j := by decide
  exact htable ⟨d, by omega⟩ i j hij

theorem step_bounds {I : Type} [Fintype I]
    (F : Fin 3 → (I → Bool) → Bool) (hF : NestedFamily F)
    (d u : ℕ) (hd : d ≤ 7)
    (hz : PairBound F false (fun i j => (profiles d).1 i j*u))
    (hy : PairBound F true (fun i j => (profiles d).2 i j*u)) :
    PairBound (step F) false (fun i j => (profiles (d+1)).1 i j*u) ∧
    PairBound (step F) true (fun i j => (profiles (d+1)).2 i j*u) := by
  have hz' : PairBound (extend F) false
      (fun i j => (profiles d).1 (clip i) (clip j)*u) := by
    intro i j hij x hx hx'; exact hz _ _ (clip_mono hij) x hx hx'
  have hy' : PairBound (extend F) true
      (fun i j => (profiles d).2 (clip i) (clip j)*u) := by
    intro i j hij x hx hx'; exact hy _ _ (clip_mono hij) x hx hx'
  constructor
  · intro q q' hqq x hx hx'
    have hc : (profiles d).2 (clip (gateIndex q')) (clip (Fin.last 3))*u ≤
        (profiles d).2 (clip (gateIndex q')) (clip (gateIndex q))*u := by
      simp only [clip_gate, clip_last]
      exact Nat.mul_le_mul_right u (profiles_order d hd _ _ (Fin.rev_le_rev.mpr hqq))
    have hh := recursive_pair_zero tournament labeling (extend F) (extend_nested hF)
      (by norm_num) _ _ hz' hy' q q' hqq hc x hx hx'
    simpa [step, profiles, Nat.add_mul, Nat.mul_assoc] using hh
  · intro q q' hqq x hx hx'
    have hh := recursive_pair_one tournament labeling.label (extend F) (extend_nested hF)
      H (cyclicTournament_outdegree H) _ _ hz' hy' q q' hqq x hx hx'
    simpa [step, profiles, Nat.add_mul, Nat.mul_assoc] using hh

abbrev LevelCoord (I : Type) : ℕ → Type
  | 0 => Fin 3 × I
  | d+1 => (Fin K × Fin 2) × LevelCoord I d

instance levelFintype (I : Type) [Fintype I] (d : ℕ) : Fintype (LevelCoord I d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype (Fin 3 × I))
  | succ d ih => exact inferInstanceAs (Fintype ((Fin K × Fin 2) × LevelCoord I d))

def levels {I : Type} (g : (I → Bool) → Bool) :
    (d : ℕ) → Fin 3 → (LevelCoord I d → Bool) → Bool
  | 0 => base g
  | d+1 => step (levels g d)

theorem levels_nested {I : Type} (g : (I → Bool) → Bool) (d : ℕ) :
    NestedFamily (levels g d) := by
  induction d with
  | zero => exact base_nested g
  | succ d ih => exact step_nested ih

theorem levels_bounds {I : Type} [Fintype I] (g : (I → Bool) → Bool) (u : ℕ)
    (h0 : ∀ x, g x = false → sensitivityAt g x ≤ u)
    (h1 : ∀ x, g x = true → sensitivityAt g x ≤ 4800*u)
    (d : ℕ) (hd : d ≤ 8) :
    PairBound (levels g d) false (fun i j => (profiles d).1 i j*u) ∧
    PairBound (levels g d) true (fun i j => (profiles d).2 i j*u) := by
  induction d with
  | zero => exact base_bounds g u h0 h1
  | succ d ih =>
    have hh := ih (by omega)
    exact step_bounds (levels g d) (levels_nested g d) d u (by omega) hh.1 hh.2

def amplify {I : Type} (g : (I → Bool) → Bool) : (LevelCoord I 8 → Bool) → Bool :=
  levels g 8 1

theorem amplify_bounds {I : Type} [Fintype I] (g : (I → Bool) → Bool) (u : ℕ)
    (h0 : ∀ x, g x = false → sensitivityAt g x ≤ u)
    (h1 : ∀ x, g x = true → sensitivityAt g x ≤ 4800*u) :
    (∀ x, amplify g x = false → sensitivityAt (amplify g) x ≤ L*u) ∧
    (∀ x, amplify g x = true → sensitivityAt (amplify g) x ≤ 4800*(L*u)) := by
  have hh := levels_bounds g u h0 h1 8 le_rfl
  constructor
  · intro x hx
    exact (hh.1.self 1 x hx).trans (Nat.mul_le_mul_right u (by
      decide))
  · intro x hx
    have hb : (profiles 8).2 1 1 ≤ 4800*L := by
      decide
    exact (hh.2.self 1 x hx).trans (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_right u hb)

end
end Sensitivity205

end Component11

-- Source component: Solutions/Blocks.lean
section Component12

open OAI.Paper320
open scoped Classical

namespace Sensitivity205
noncomputable section

structure Blocks {I : Type} {h : ℕ} (F : Fin h → (I → Bool) → Bool) (n : ℕ) where
  zero : ∀ q, F q (fun _ => false) = false
  sets : Fin n → Finset I
  nonempty : ∀ i, (sets i).Nonempty
  disjoint : Pairwise fun i j => Disjoint (sets i) (sets j)
  on : ∀ q i, F q (flip (fun _ => false) (sets i)) = true

theorem threshold_false (q : Fin 3) : threshold q (fun _ => false) = false := by
  fin_cases q <;> decide

theorem threshold_true (q : Fin 3) : threshold q (fun _ => true) = true := by
  fin_cases q <;> decide

def baseBlocks {I : Type} {g : (I → Bool) → Bool} {n : ℕ}
    (w : Blocks (fun _ : Fin 1 => g) n) : Blocks (base g) n where
  zero q := by
    change threshold q (fun _ => g (fun _ => false)) = false
    simp only [w.zero 0]
    exact threshold_false q
  sets i := Finset.univ.product (w.sets i)
  nonempty i := by
    obtain ⟨a, ha⟩ := w.nonempty i
    exact ⟨(0,a), Finset.mem_product.mpr ⟨Finset.mem_univ _,ha⟩⟩
  disjoint := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact Finset.disjoint_left.mp (w.disjoint hij)
      (Finset.mem_product.mp hp).2 (Finset.mem_product.mp hq).2
  on q i := by
    have he (j : Fin 3) :
        (fun a => flip (fun _ => false) (Finset.univ.product (w.sets i)) (j,a)) =
          flip (fun _ => false) (w.sets i) := by
      funext a; simp [OAI.Paper320.flip]
    change threshold q (fun j => g (fun a =>
      flip (fun _ => false) (Finset.univ.product (w.sets i)) (j,a))) = true
    simp only [he, w.on 0 i]
    exact threshold_true q

def stepBlocks {I : Type} {F : Fin 3 → (I → Bool) → Bool} {n : ℕ}
    (w : Blocks F n) : Blocks (step F) (K*n) where
  zero q := recursiveFamily_zero tournament labeling.label (extend F) (by norm_num)
    (fun j => w.zero (clip j)) q
  sets i := rowLift (finProdFinEquiv.symm i).1 (w.sets (finProdFinEquiv.symm i).2)
  nonempty i := by
    obtain ⟨a, ha⟩ := w.nonempty (finProdFinEquiv.symm i).2
    exact ⟨(((finProdFinEquiv.symm i).1,0),a), (mem_rowLift _ _ _).mpr ⟨rfl,ha⟩⟩
  disjoint := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hi := (mem_rowLift _ _ _).mp hp
    have hj := (mem_rowLift _ _ _).mp hq
    have he : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1 := hi.1.symm.trans hj.1
    have hne : (finProdFinEquiv.symm i).2 ≠ (finProdFinEquiv.symm j).2 := by
      intro he'
      exact hij (finProdFinEquiv.symm.injective (Prod.ext he he'))
    exact Finset.disjoint_left.mp (w.disjoint hne) hi.2 hj.2
  on q i := recursiveFamily_rowLift tournament labeling.label (extend F)
    (fun j => w.zero (clip j)) _ (fun j => w.on (clip j) _) _ q

def levelsBlocks {I : Type} {g : (I → Bool) → Bool} {n : ℕ}
    (w : Blocks (fun _ : Fin 1 => g) n) :
    (d : ℕ) → Blocks (levels g d) (K^d*n)
  | 0 => by simpa [levels] using baseBlocks w
  | d+1 => by
    simpa [levels, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      stepBlocks (levelsBlocks w d)

def amplifyBlocks {I : Type} {g : (I → Bool) → Bool} {n : ℕ}
    (w : Blocks (fun _ : Fin 1 => g) n) : Blocks (fun _ : Fin 1 => amplify g) (B*n) where
  zero _ := (levelsBlocks w 8).zero 1
  sets := (levelsBlocks w 8).sets
  nonempty := (levelsBlocks w 8).nonempty
  disjoint := (levelsBlocks w 8).disjoint
  on _ := (levelsBlocks w 8).on 1

abbrev IterCoord : ℕ → Type
  | 0 => Fin 1
  | m+1 => LevelCoord (IterCoord m) 8

instance iterFintype (m : ℕ) : Fintype (IterCoord m) := by
  induction m with
  | zero => exact inferInstanceAs (Fintype (Fin 1))
  | succ m ih => exact levelFintype (IterCoord m) 8

def iter : (m : ℕ) → (IterCoord m → Bool) → Bool
  | 0 => fun x => x 0
  | m+1 => amplify (iter m)

def iterBlocks : (m : ℕ) → Blocks (fun _ : Fin 1 => iter m) (B^m)
  | 0 => {
      zero := fun _ => rfl
      sets := fun _ => {0}
      nonempty := fun _ => Finset.singleton_nonempty _
      disjoint := by intro i j hij; have he : i = j := by apply Fin.ext; have := i.isLt; have := j.isLt; simp at *
                     exact False.elim (hij he)
      on := by intro q i; simp [iter, OAI.Paper320.flip] }
  | m+1 => by simpa [iter, pow_succ, Nat.mul_comm] using amplifyBlocks (iterBlocks m)

theorem iter_sides (m : ℕ) :
    (∀ x, iter m x = false → sensitivityAt (iter m) x ≤ L^m) ∧
    (∀ x, iter m x = true → sensitivityAt (iter m) x ≤ 4800*L^m) := by
  induction m with
  | zero =>
    constructor <;> intro x hx
    · exact (sensitivityAt_le_card _ _).trans (by simp [IterCoord])
    · exact (sensitivityAt_le_card _ _).trans (by simp [IterCoord])
  | succ m ih =>
    simpa [iter, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      amplify_bounds (iter m) (L^m) ih.1 ih.2

theorem iter_sensitivity (m : ℕ) : sensitivity (iter m) ≤ 4800*L^m := by
  apply sensitivity_le
  intro x
  cases hx : iter m x
  · exact ((iter_sides m).1 x hx).trans (by omega)
  · exact (iter_sides m).2 x hx

theorem iter_blocksensitivity (m : ℕ) : B^m ≤ blockSensitivityAt (iter m) (fun _ => false) := by
  have w := iterBlocks m
  simpa only [Fintype.card_fin] using
    le_blockSensitivityAt_of_family (iter m) (fun _ => false) w.sets w.nonempty w.disjoint
      (fun i => by rw [w.on 0 i, w.zero 0]; decide)

end
end Sensitivity205

end Component12

-- Source component: Solutions/Result.lean
section Component13

open OAI.Paper320
open scoped Classical

set_option maxRecDepth 10000

namespace Sensitivity205
noncomputable section

set_option maxRecDepth 10000 in
theorem arithmetic_gap : 4*L^41 ≤ B^20 := by
  decide

set_option maxRecDepth 10000 in
theorem initial_factor : 4800^41 ≤ (4:ℕ)^1024 := by
  decide

theorem pow_exchange (a m n : ℕ) : (a^m)^n = (a^n)^m := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm m n]

theorem seed_power : (4800*L^1024)^41 ≤ (B^1024)^20 := by
  calc
    (4800*L^1024)^41 = 4800^41 * (L^41)^1024 := by
      rw [mul_pow, pow_exchange L 1024 41]
    _ ≤ 4^1024 * (L^41)^1024 := Nat.mul_le_mul_right _ initial_factor
    _ = (4*L^41)^1024 := (mul_pow _ _ _).symm
    _ ≤ (B^20)^1024 := Nat.pow_le_pow_left arithmetic_gap _
    _ = (B^1024)^20 := pow_exchange B 20 1024

theorem seed_real_power : ((4800*L^1024 : ℕ) : ℝ) ^ (2.05 : ℝ) ≤
    ((B^1024 : ℕ) : ℝ) := by
  have h := seed_power
  have hr : (((4800*L^1024 : ℕ) : ℝ))^41 ≤ (((B^1024 : ℕ) : ℝ))^20 := by
    exact_mod_cast h
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Nat.cast_nonneg _) (by norm_num : (20:ℕ) ≠ 0)).mp
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _),
    show (2.05 : ℝ) * (20:ℕ) = ((41:ℕ):ℝ) by norm_num,
    Real.rpow_natCast]
  exact hr

theorem finite_seed (m : ℕ) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      sensitivity f ≤ 4800*L^m ∧ B^m ≤ blockSensitivityAt f (fun _ => false) := by
  let e := Fintype.equivFin (IterCoord m)
  refine ⟨Fintype.card (IterCoord m), reindex e (iter m), ?_, ?_⟩
  · rw [sensitivity_reindex]; exact iter_sensitivity m
  · rw [blockSensitivityAt_reindex]; exact iter_blocksensitivity m

set_option maxRecDepth 10000 in
theorem achieves_205 : SensitivityCampaign.AchievesExponent (2.05 : ℝ) := by
  obtain ⟨n, f, hs, hb⟩ := finite_seed 1024
  apply SensitivityCampaign.finite_certificate f (fun _ => false)
    (4800*L^1024) (B^1024) (2.05:ℝ) _ _ (by norm_num) hs hb seed_real_power
  · have hp : 0 < L^1024 := pow_pos (by norm_num [L]) _
    omega
  · exact one_lt_pow₀ (by norm_num [B, K]) (by norm_num)

end
end Sensitivity205

theorem solution : SensitivityCampaign.AchievesExponent (2.05 : ℝ) :=
  Sensitivity205.achieves_205

#print axioms solution

end Component13

