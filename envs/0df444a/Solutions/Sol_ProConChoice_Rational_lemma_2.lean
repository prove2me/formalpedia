-- Prove2me | solution 1 for ProConChoice.Rational.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:42:16.420307+00:00
-- url     : https://prove2.me/submissions/f03974e3-c825-4638-a546-97d590652e21

import Mathlib
set_option autoImplicit false

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (p q : X → Finset X → ℝ) (a : X) :
    (∀ S : Finset X, a ∈ S →
        p a S = ∑ T ∈ (Finset.univ : Finset X).powerset.filter (fun T => S ⊆ T), q a T) ↔
    (∀ S : Finset X, a ∈ S →
        q a S = ∑ T ∈ (Finset.univ : Finset X).powerset.filter (fun T => S ⊆ T),
          (-1 : ℝ) ^ (T.card - S.card) * p a T) := by
  have hsup : ∀ S : Finset X, (Finset.univ : Finset X).powerset.filter (fun T => S ⊆ T)
      = Finset.Icc S Finset.univ := by
    intro S; ext T; simp [Finset.mem_Icc]
  simp_rw [hsup]
  have K : ∀ S U : Finset X, S ⊆ U →
      ∑ T ∈ Finset.Icc S U, (-1 : ℝ) ^ (T.card - S.card) = if S = U then 1 else 0 := by
    intro S U hSU
    rw [Finset.Icc_eq_image_powerset hSU, Finset.sum_image]
    · have : ∀ R ∈ (U \ S).powerset, (-1 : ℝ) ^ ((S ∪ R).card - S.card) = (-1) ^ R.card := by
        intro R hR
        rw [Finset.mem_powerset] at hR
        have hd : Disjoint S R := by
          rw [Finset.disjoint_left]
          intro x hx hxR
          have := hR hxR
          simp at this
          exact this.2 hx
        rw [Finset.card_union_of_disjoint hd]; simp
      have hz : ∑ R ∈ (U \ S).powerset, (-1 : ℝ) ^ R.card = if U \ S = ∅ then 1 else 0 := by
        have := congrArg (fun z : ℤ => (z : ℝ)) (Finset.sum_powerset_neg_one_pow_card (x := U \ S))
        simp only [Int.cast_sum, Int.cast_pow, Int.cast_neg, Int.cast_one] at this
        rw [this]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl this, hz]
      by_cases h : S = U
      · subst h; simp
      · have : U \ S ≠ ∅ := by
          intro h'
          apply h
          exact Finset.Subset.antisymm hSU (Finset.sdiff_eq_empty_iff_subset.mp h')
        simp [this, h]
    · intro R1 hR1 R2 hR2 h
      simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at hR1 hR2
      have d1 : Disjoint S R1 := by
        rw [Finset.disjoint_left]
        intro x hx hxR
        have := hR1 hxR
        simp at this
        exact this.2 hx
      have d2 : Disjoint S R2 := by
        rw [Finset.disjoint_left]
        intro x hx hxR
        have := hR2 hxR
        simp at this
        exact this.2 hx
      have e1 := Finset.union_sdiff_cancel_left d1
      have e2 := Finset.union_sdiff_cancel_left d2
      simp only at h
      rw [← e1, ← e2, h]
  have K2 : ∀ S U : Finset X, S ⊆ U →
      ∑ T ∈ Finset.Icc S U, (-1 : ℝ) ^ (U.card - T.card) = if S = U then 1 else 0 := by
    intro S U hSU
    have : ∀ T ∈ Finset.Icc S U, (-1 : ℝ) ^ (U.card - T.card)
        = (-1) ^ (U.card - S.card) * (-1) ^ (T.card - S.card) := by
      intro T hT
      rw [Finset.mem_Icc] at hT
      have h1 := Finset.card_le_card hT.1
      have h2 := Finset.card_le_card hT.2
      have : U.card - S.card = (U.card - T.card) + (T.card - S.card) := by omega
      rw [this, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, K S U hSU]
    by_cases h : S = U
    · subst h; simp
    · simp [h]
  have swap : ∀ (S : Finset X) (f : Finset X → Finset X → ℝ),
      ∑ T ∈ Finset.Icc S Finset.univ, ∑ U ∈ Finset.Icc T Finset.univ, f T U
      = ∑ U ∈ Finset.Icc S Finset.univ, ∑ T ∈ Finset.Icc S U, f T U := by
    intro S f
    apply Finset.sum_comm'
    intro T U
    simp only [Finset.mem_Icc, Finset.subset_univ, and_true]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, h1.trans h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2⟩
  constructor
  · intro h S hS
    have e : ∑ T ∈ Finset.Icc S Finset.univ, (-1 : ℝ) ^ (T.card - S.card) * p a T
        = ∑ T ∈ Finset.Icc S Finset.univ, ∑ U ∈ Finset.Icc T Finset.univ,
            (-1 : ℝ) ^ (T.card - S.card) * q a U := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.mem_Icc] at hT
      rw [h T (hT.1 hS), Finset.mul_sum]
    rw [e, swap]
    have e2 : ∀ U ∈ Finset.Icc S Finset.univ,
        ∑ T ∈ Finset.Icc S U, (-1 : ℝ) ^ (T.card - S.card) * q a U
        = if S = U then q a U else 0 := by
      intro U hU
      rw [Finset.mem_Icc] at hU
      rw [← Finset.sum_mul, K S U hU.1]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl e2]
    rw [Finset.sum_ite_eq]
    simp
  · intro h S hS
    have e : ∑ T ∈ Finset.Icc S Finset.univ, q a T
        = ∑ T ∈ Finset.Icc S Finset.univ, ∑ U ∈ Finset.Icc T Finset.univ,
            (-1 : ℝ) ^ (U.card - T.card) * p a U := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.mem_Icc] at hT
      rw [h T (hT.1 hS)]
    rw [e, swap]
    have e2 : ∀ U ∈ Finset.Icc S Finset.univ,
        ∑ T ∈ Finset.Icc S U, (-1 : ℝ) ^ (U.card - T.card) * p a U
        = if S = U then p a U else 0 := by
      intro U hU
      rw [Finset.mem_Icc] at hU
      rw [← Finset.sum_mul, K2 S U hU.1]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl e2]
    rw [Finset.sum_ite_eq]
    simp
