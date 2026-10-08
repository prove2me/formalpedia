-- Prove2me | solution 1 for WeightedRootIntegralIdentity.weightedRootProveJumpIdentity
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T07:06:11.494677+00:00
-- url     : https://prove2.me/submissions/8e2c2c39-97b6-44e2-88d1-dd2475a067cc

import Mathlib
open scoped Interval

theorem solution
    (F : ℝ → ℂ) (a₀ a₁ : ℝ) (A : ℂ)
    (hA : A = Complex.I *
      (((∫ x in a₀..a₁, (F x).im / x) : ℝ) : ℂ)) :
    A - starRingEnd ℂ A =
      2 * Complex.I * (((∫ x in a₀..a₁, (F x).im / x) : ℝ) : ℂ) := by
  rw [hA]
  simp [map_mul, sub_eq_add_neg]
  ring
