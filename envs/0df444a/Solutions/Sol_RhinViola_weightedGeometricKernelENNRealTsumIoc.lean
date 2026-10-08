-- Prove2me | solution 1 for RhinViola.weightedGeometricKernelENNRealTsumIoc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T09:27:35.254587+00:00
-- url     : https://prove2.me/submissions/ad109cef-20db-4163-b514-cf323755c65e

import Theorems.Thm_RhinViola_weightedGeometricKernelENNRealTsum
import Mathlib.Tactic

theorem solution
    (h m : ℕ) (x y : ℝ)
    (hx : x ∈ Set.Ioc (0 : ℝ) 1)
    (hy : y ∈ Set.Ioc (0 : ℝ) 1)
    (hx1 : x ≠ 1) :
    (∑' k : ℕ,
      ENNReal.ofReal (x ^ (h + k)) *
        ENNReal.ofReal (y ^ (m + k))) =
      ENNReal.ofReal (x ^ h * y ^ m / (1 - x * y)) := by
  have hx0 : 0 ≤ x := le_of_lt hx.1
  have hy0 : 0 ≤ y := le_of_lt hy.1
  have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
  have hxy_le : x * y ≤ x * 1 := by
    exact mul_le_mul_of_nonneg_left hy.2 hx0
  have hxy : x * y < 1 := by
    nlinarith
  exact RhinViola.weightedGeometricKernelENNRealTsum h m x y hx0 hy0 hxy
