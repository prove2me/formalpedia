-- Prove2me | solution 1 for WeightedRootIntegralIdentity.missionBankParametrization
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T10:30:46.717632+00:00
-- url     : https://prove2.me/submissions/7e6ba6cc-4602-4819-8f11-1ffb1a4250c3

import Mathlib
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (a : ℕ → ℝ) (k : ℕ)
    (U L : ℝ)
    (hU : U = (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
      ∫ x in a k..a (k + 1),
        (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x)
    (hL : L = -((Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
      ∫ x in a k..a (k + 1),
        (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x)) :
    U + L = 0 := by
  rw [hU, hL]
  ring
