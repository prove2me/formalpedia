-- Prove2me | solution 1 for WeierstrassEllipticZeta.optimal_anchor_weight_selection
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T18:42:37.09401+00:00
-- url     : https://prove2.me/submissions/469de512-f1f3-4392-9594-f355c8cc754a

import Definitions.Def_WeierstrassEllipticZeta_OptimalAnchorWeight
import Mathlib.Tactic

noncomputable section
open scoped Classical
namespace WeierstrassEllipticZeta

private theorem point_class_count (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) : candidateClassCount Λ η X (.inl ()) = X.card := by
  unfold candidateClassCount
  change (X.image (⊥ : Submodule ℤ ℂ).mkQ).card = X.card
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  have : x - y ∈ (⊥ : Submodule ℤ ℂ) := (Submodule.Quotient.eq _).mp hxy
  exact sub_eq_zero.mp (by simpa using this)

private theorem weight_scale (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (m : ℕ) (k : FiniteLocusCandidate Λ X) :
    candidateWeight Λ η X m k * (elementaryDegree (candidateLocusShape Λ η X k) m + 1) =
      candidateClassCount Λ η X k * (m + 1) := by
  rcases k with u | u | p <;>
    simp [candidateWeight, candidateLocusShape, elementaryDegree, Nat.mul_comm]

theorem optimal_anchor_weight_spec (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) :
    sparseAnchorWeight Λ η X S Q m n K Z
        (optimalSparseAnchor Λ η X S Q m n K Z) =
      minimumAnchorWeight Λ η X S Q m n K Z := by
  unfold optimalSparseAnchor
  exact Classical.choose_spec (show ∃ a : SparseGCDAnchorCandidate Λ η X S Q m n K Z,
      sparseAnchorWeight Λ η X S Q m n K Z a =
        minimumAnchorWeight Λ η X S Q m n K Z from
    Nat.find_spec (show ∃ w : ℕ, ∃ a : SparseGCDAnchorCandidate Λ η X S Q m n K Z,
        sparseAnchorWeight Λ η X S Q m n K Z a = w from
      ⟨sparseAnchorWeight Λ η X S Q m n K Z (.inl ()), .inl (), rfl⟩))

private theorem minimum_weight_le (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ)
    (a : SparseGCDAnchorCandidate Λ η X S Q m n K Z) :
    minimumAnchorWeight Λ η X S Q m n K Z ≤
      sparseAnchorWeight Λ η X S Q m n K Z a := by
  unfold minimumAnchorWeight
  exact Nat.find_min' _ ⟨a, rfl⟩

private theorem minimum_weight_le_card (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) :
    minimumAnchorWeight Λ η X S Q m n K Z ≤ X.card := by
  simpa [sparseAnchorWeight, sparseGCDAnchorLocus, candidateWeight, point_class_count] using
    minimum_weight_le Λ η X S Q m n K Z (.inl ())

private theorem candidate_budget_iff (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (m n E : ℕ) (C : ℝ) (k : FiniteLocusCandidate Λ X) :
    (((candidateClassCount Λ η X k * E : ℕ) : ℝ) ≤
      C * (((elementaryDegree (candidateLocusShape Λ η X k) m + 1) * n ^ 2 : ℕ) : ℝ)) ↔
    (((candidateWeight Λ η X m k * E : ℕ) : ℝ) ≤
      C * (((m + 1) * n ^ 2 : ℕ) : ℝ)) := by
  have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hd : (0 : ℝ) < (elementaryDegree (candidateLocusShape Λ η X k) m + 1 : ℕ) :=
    by positivity
  have he : (candidateWeight Λ η X m k : ℝ) *
      (elementaryDegree (candidateLocusShape Λ η X k) m + 1 : ℕ) =
      (candidateClassCount Λ η X k : ℝ) * (m + 1 : ℕ) := by
    exact_mod_cast weight_scale Λ η X m k
  simp only [Nat.cast_mul] at *
  constructor
  · intro h
    apply (mul_le_mul_iff_right₀ hd).mp
    calc
      _ = ((candidateClassCount Λ η X k : ℝ) * E) * (m + 1 : ℕ) := by
        linear_combination (E : ℝ) * he
      _ ≤ (C * ((elementaryDegree (candidateLocusShape Λ η X k) m + 1 : ℕ) * (n ^ 2 : ℕ))) *
          (m + 1 : ℕ) := mul_le_mul_of_nonneg_right h hm.le
      _ = _ := by ring
  · intro h
    apply (mul_le_mul_iff_right₀ hm).mp
    calc
      _ = ((candidateWeight Λ η X m k : ℝ) * E) *
          (elementaryDegree (candidateLocusShape Λ η X k) m + 1 : ℕ) := by
        linear_combination -(E : ℝ) * he
      _ ≤ (C * ((m + 1 : ℕ) * (n ^ 2 : ℕ))) *
          (elementaryDegree (candidateLocusShape Λ η X k) m + 1 : ℕ) :=
        mul_le_mul_of_nonneg_right h hd.le
      _ = _ := by ring

private theorem minimum_weight_pos (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) (hX : X.Nonempty) :
    1 ≤ minimumAnchorWeight Λ η X S Q m n K Z := by
  rw [← optimal_anchor_weight_spec]
  unfold sparseAnchorWeight
  generalize sparseGCDAnchorLocus Λ η X S Q m n K Z
    (optimalSparseAnchor Λ η X S Q m n K Z) = k
  have hk : 0 < candidateClassCount Λ η X k :=
    Finset.card_pos.mpr (hX.image _)
  rcases k with u | u
  · simpa [candidateWeight] using Nat.succ_le_of_lt hk
  · simp only [candidateWeight]
    exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) hk)

private theorem minimizing_nonpoint_class_bound
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ)
    (a : SparseGCDAnchorCandidate Λ η X S Q m n K Z)
    (ha : sparseAnchorWeight Λ η X S Q m n K Z a =
      minimumAnchorWeight Λ η X S Q m n K Z)
    (hd : elementaryDegree (candidateLocusShape Λ η X
      (sparseGCDAnchorLocus Λ η X S Q m n K Z a)) m = 0) :
    candidateClassCount Λ η X (sparseGCDAnchorLocus Λ η X S Q m n K Z a) ≤
      X.card / (m + 1) := by
  have hb := minimum_weight_le_card Λ η X S Q m n K Z
  have hs := weight_scale Λ η X m (sparseGCDAnchorLocus Λ η X S Q m n K Z a)
  rw [hd, zero_add, mul_one] at hs
  change sparseAnchorWeight Λ η X S Q m n K Z a = _ at hs
  rw [ha] at hs
  exact (Nat.le_div_iff_mul_le (Nat.succ_pos m)).mpr (hs ▸ hb)

private theorem minimum_budget_iff (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) (E : ℕ) (C : ℝ) :
    (∃ a : SparseGCDAnchorCandidate Λ η X S Q m n K Z,
      (((X.image (elementaryPeriodKernel Λ η (candidateLocusShape Λ η X
        (sparseGCDAnchorLocus Λ η X S Q m n K Z a))).mkQ).card * E : ℕ) : ℝ) ≤
        C * (((elementaryDegree (candidateLocusShape Λ η X
          (sparseGCDAnchorLocus Λ η X S Q m n K Z a)) m + 1) * n ^ 2 : ℕ) : ℝ)) ↔
    (((minimumAnchorWeight Λ η X S Q m n K Z * E : ℕ) : ℝ) ≤
      C * (((m + 1) * n ^ 2 : ℕ) : ℝ)) := by
  constructor
  · rintro ⟨a, ha⟩
    have hscaled := (candidate_budget_iff Λ η X m n E C
      (sparseGCDAnchorLocus Λ η X S Q m n K Z a)).mp ha
    have hw := Nat.mul_le_mul_right E (minimum_weight_le Λ η X S Q m n K Z a)
    have hwR : ((minimumAnchorWeight Λ η X S Q m n K Z * E : ℕ) : ℝ) ≤
        ((sparseAnchorWeight Λ η X S Q m n K Z a * E : ℕ) : ℝ) := by exact_mod_cast hw
    exact hwR.trans hscaled
  · intro h
    refine ⟨optimalSparseAnchor Λ η X S Q m n K Z, ?_⟩
    apply (candidate_budget_iff Λ η X m n E C _).mpr
    change (((sparseAnchorWeight Λ η X S Q m n K Z
      (optimalSparseAnchor Λ η X S Q m n K Z) * E : ℕ) : ℝ) ≤ _)
    rw [optimal_anchor_weight_spec]
    exact h


end WeierstrassEllipticZeta
open WeierstrassEllipticZeta

theorem solution
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) :
    (minimumAnchorWeight Λ η X S Q m n K Z ≤ X.card ∧
      (X.Nonempty → 1 ≤ minimumAnchorWeight Λ η X S Q m n K Z) ∧
      sparseAnchorWeight Λ η X S Q m n K Z
        (optimalSparseAnchor Λ η X S Q m n K Z) =
          minimumAnchorWeight Λ η X S Q m n K Z ∧
      (∀ a : SparseGCDAnchorCandidate Λ η X S Q m n K Z,
        minimumAnchorWeight Λ η X S Q m n K Z ≤
          sparseAnchorWeight Λ η X S Q m n K Z a) ∧
      (∀ a : SparseGCDAnchorCandidate Λ η X S Q m n K Z,
        sparseAnchorWeight Λ η X S Q m n K Z a =
          minimumAnchorWeight Λ η X S Q m n K Z →
        elementaryDegree (candidateLocusShape Λ η X
          (sparseGCDAnchorLocus Λ η X S Q m n K Z a)) m = 0 →
        candidateClassCount Λ η X (sparseGCDAnchorLocus Λ η X S Q m n K Z a) ≤
          X.card / (m + 1))) ∧
    ∀ (E : ℕ) (C : ℝ),
      (∃ a : SparseGCDAnchorCandidate Λ η X S Q m n K Z,
        (((X.image (elementaryPeriodKernel Λ η (candidateLocusShape Λ η X
          (sparseGCDAnchorLocus Λ η X S Q m n K Z a))).mkQ).card * E : ℕ) : ℝ) ≤
          C * (((elementaryDegree (candidateLocusShape Λ η X
            (sparseGCDAnchorLocus Λ η X S Q m n K Z a)) m + 1) * n ^ 2 : ℕ) : ℝ)) ↔
      (((minimumAnchorWeight Λ η X S Q m n K Z * E : ℕ) : ℝ) ≤
        C * (((m + 1) * n ^ 2 : ℕ) : ℝ)) := by
  exact ⟨⟨minimum_weight_le_card Λ η X S Q m n K Z,
    minimum_weight_pos Λ η X S Q m n K Z,
    optimal_anchor_weight_spec Λ η X S Q m n K Z,
    minimum_weight_le Λ η X S Q m n K Z,
    minimizing_nonpoint_class_bound Λ η X S Q m n K Z⟩,
    minimum_budget_iff Λ η X S Q m n K Z⟩
