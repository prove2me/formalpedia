-- Prove2me | solution 1 for WeightedRootIntegralIdentity.bankRealIntegralAndOriginDerivative
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T10:59:12.953986+00:00
-- url     : https://prove2.me/submissions/76320957-08f5-4577-b3dc-c00f83c9c9bd

import Mathlib
open scoped BigOperators Interval

theorem solution
    (n : ℕ) (a : ℕ → ℝ) (B : ℝ) (d : ℂ)
    (hB : B = ∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x)
    (hd : d.re = -((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i)) :
    B = ∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * ((k + 1 : ℝ) / n)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| ((n : ℝ)⁻¹)) / x ∧
    d.re = -((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i) := by
  exact ⟨hB, hd⟩
