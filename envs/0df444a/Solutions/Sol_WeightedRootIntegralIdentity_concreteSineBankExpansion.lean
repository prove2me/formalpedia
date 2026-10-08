-- Prove2me | solution 1 for WeightedRootIntegralIdentity.concreteSineBankExpansion
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T10:26:13.719454+00:00
-- url     : https://prove2.me/submissions/fbd6d01b-f0da-434e-84ec-fd9189b1cf91

import Mathlib
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (a : ℕ → ℝ)
    (B : ℝ)
    (hB : B = ∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x) :
    B = ∑ k ∈ Finset.range (n - 1),
      ((Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) : ℝ) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x := by
  exact hB
