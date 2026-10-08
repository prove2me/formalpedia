-- Prove2me | solution 1 for WeightedRootIntegralIdentity.missionFinalConstantNormalization
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T07:46:18.098778+00:00
-- url     : https://prove2.me/submissions/71ab6946-fdbb-4924-9ec6-15ef41363612

import Mathlib
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (a : ℕ → ℝ) (B : ℝ)
    (hB : B = ∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x)
    (hbalance : B = ((1 : ℝ) / n) * (∑ i ∈ Finset.range n, a i)
      - Real.rpow (∏ i ∈ Finset.range n, a i) ((n : ℝ)⁻¹)) :
    (∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x)
      = ((1 : ℝ) / n) * (∑ i ∈ Finset.range n, a i)
        - Real.rpow (∏ i ∈ Finset.range n, a i) ((n : ℝ)⁻¹) := by
  exact hB.symm.trans hbalance
