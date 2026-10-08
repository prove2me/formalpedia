-- Prove2me | solution 1 for WeightedRootIntegralIdentity.missionJumpAndResidueSpecialization
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T10:34:33.718662+00:00
-- url     : https://prove2.me/submissions/843e4a82-5611-4e8a-aafb-6806c4507fa4

import Mathlib
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (a : ℕ → ℝ) (J B d p : ℂ)
    (hbank : J = 2 * B)
    (hB : B = ∑ k ∈ Finset.range (n - 1),
      ((Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) : ℂ) *
        (((∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x) : ℝ) : ℂ))
    (hd : d.re = -((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i))
    (hp : p.re = -Real.rpow (∏ i ∈ Finset.range n, a i) ((n : ℝ)⁻¹)) :
    J = 2 * ∑ k ∈ Finset.range (n - 1),
      ((Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) : ℂ) *
        (((∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x) : ℝ) : ℂ) ∧
    d.re = -((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) ∧
    p.re = -Real.rpow (∏ i ∈ Finset.range n, a i) ((n : ℝ)⁻¹) := by
  constructor
  · rw [hbank, hB]
  · exact ⟨hd, hp⟩
