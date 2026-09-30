-- Prove2me | solution 1 for WeierstrassEllipticZeta.fibre_present_minimum_anchor_weight
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-23T02:02:44.58518+00:00
-- url     : https://prove2.me/submissions/c71a937a-3ed7-4ebb-880f-4048ff486963

import Theorems.Thm_WeierstrassEllipticZeta_optimal_anchor_weight_selection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

noncomputable section
open scoped Classical
namespace WeierstrassEllipticZeta

private lemma quotient_image_card_mono (K Λ : Submodule ℤ ℂ) (hK : K ≤ Λ)
    (X : Finset ℂ) : (X.image Λ.mkQ).card ≤ (X.image K.mkQ).card := by
  let f : (ℂ ⧸ K) →ₗ[ℤ] (ℂ ⧸ Λ) :=
    K.mapQ Λ LinearMap.id (by simpa using hK)
  have heq : (X.image K.mkQ).image f = X.image Λ.mkQ := by
    rw [Finset.image_image]
    rfl
  rw [← heq]
  exact Finset.card_image_le

private lemma shape_kernel_le (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (shape : ElementaryLocusShape) : elementaryPeriodKernel Λ η shape ≤ Λ := by
  cases shape with
  | point => exact bot_le
  | fibre => exact le_rfl
  | line α =>
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hz
    exact v.property

private lemma point_weight (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (m : ℕ) : candidateWeight Λ η X m (.inl ()) = X.card := by
  change (X.image (⊥ : Submodule ℤ ℂ).mkQ).card = X.card
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  have h := (Submodule.Quotient.eq (⊥ : Submodule ℤ ℂ)).mp hxy
  exact sub_eq_zero.mp (by simpa using h)

private lemma weight_lower_bound (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (m : ℕ) (k : FiniteLocusCandidate Λ X) :
    min X.card ((m + 1) * (X.image Λ.mkQ).card) ≤ candidateWeight Λ η X m k := by
  rcases k with u | k
  · cases u
    rw [point_weight]
    exact Nat.min_le_left _ _
  · change min X.card ((m + 1) * (X.image Λ.mkQ).card) ≤
      (m + 1) * candidateClassCount Λ η X (.inr k)
    apply (Nat.min_le_right _ _).trans
    apply Nat.mul_le_mul_left
    exact quotient_image_card_mono _ Λ
      (shape_kernel_le Λ η (candidateLocusShape Λ η X (.inr k))) X


end WeierstrassEllipticZeta
open WeierstrassEllipticZeta

theorem solution
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ) (K : Set ℂ) (Z : Finset ℂ) :
    min X.card ((m + 1) * (X.image Λ.mkQ).card) ≤
        minimumAnchorWeight Λ η X S Q m n K Z ∧
      (X.card ≤ (m + 1) * (X.image Λ.mkQ).card →
        minimumAnchorWeight Λ η X S Q m n K Z = X.card) ∧
      (Z.Nonempty → minimumAnchorWeight Λ η X S Q m n K Z =
        min X.card ((m + 1) * (X.image Λ.mkQ).card)) := by
  have hs := (optimal_anchor_weight_selection Λ η X S Q m n K Z).1
  have hlow : min X.card ((m + 1) * (X.image Λ.mkQ).card) ≤
      minimumAnchorWeight Λ η X S Q m n K Z := by
    rw [← hs.2.2.1]
    exact weight_lower_bound Λ η X m
      (sparseGCDAnchorLocus Λ η X S Q m n K Z
        (optimalSparseAnchor Λ η X S Q m n K Z))
  refine ⟨hlow, ?_, ?_⟩
  · intro hpoint
    exact le_antisymm hs.1 (by simpa [Nat.min_eq_left hpoint] using hlow)
  · rintro ⟨z, hz⟩
    have hfibre : minimumAnchorWeight Λ η X S Q m n K Z ≤
        (m + 1) * (X.image Λ.mkQ).card := by
      have h := hs.2.2.2.1 (.inr (.inl ⟨z, hz⟩))
      exact h
    exact le_antisymm (le_min hs.1 hfibre) hlow
