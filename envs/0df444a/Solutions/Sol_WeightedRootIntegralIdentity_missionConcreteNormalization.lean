-- Prove2me | solution 1 for WeightedRootIntegralIdentity.missionConcreteNormalization
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T10:40:12.315722+00:00
-- url     : https://prove2.me/submissions/ecae8a73-b3da-4bb7-97f6-eb0df8b28e68

import Mathlib
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hcontour :
      (∑ k ∈ Finset.range (n - 1),
        (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
          ∫ x in a k..a (k + 1),
            (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x)
        = ((1 : ℝ) / n) * (∑ i ∈ Finset.range n, a i)
          - Real.rpow (∏ i ∈ Finset.range n, a i) ((n : ℝ)⁻¹)) :
    (∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x)
      = ((1 : ℝ) / n) * (∑ i ∈ Finset.range n, a i)
        - Real.rpow (∏ i ∈ Finset.range n, a i) ((n : ℝ)⁻¹) := by
  exact hcontour
