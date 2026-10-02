-- Prove2me | solution 1 for ShorNonsmooth.Subdiff.isMinOn_iff_zero_mem_subdifferential
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T09:05:22.669318+00:00
-- url     : https://prove2.me/submissions/b3815bfa-d390-4170-8bdd-8f8b5d3f02a9

import Mathlib
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential

open ShorNonsmooth.Subdiff

theorem solution {n : ℕ}
    (M : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (_hf : ConvexOn ℝ M f) (x₀ : EuclideanSpace ℝ (Fin n)) (_hx₀ : x₀ ∈ interior M) :
    (∀ x ∈ M, f x₀ ≤ f x) ↔ (0 : EuclideanSpace ℝ (Fin n)) ∈ subdifferential M f x₀ := by
  constructor
  · intro hmin
    change IsSubgradient M f x₀ 0
    intro x hx
    have : f x - f x₀ ≥ 0 := sub_nonneg.mpr (hmin x hx)
    simpa [inner_zero_left] using this
  · intro h0 x hx
    have hsg : IsSubgradient M f x₀ 0 := h0
    have := hsg x hx
    simpa [inner_zero_left, sub_nonneg] using this
