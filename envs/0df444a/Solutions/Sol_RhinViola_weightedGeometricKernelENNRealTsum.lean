-- Prove2me | solution 1 for RhinViola.weightedGeometricKernelENNRealTsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T23:17:10.013984+00:00
-- url     : https://prove2.me/submissions/275c8edf-c5d2-4027-bcb9-c3804ba2031e

import Theorems.Thm_RhinViola_weightedGeometricKernelHasSum
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

theorem solution
    (h m : ℕ) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x * y < 1) :
    (∑' k : ℕ,
      ENNReal.ofReal (x ^ (h + k)) *
        ENNReal.ofReal (y ^ (m + k))) =
      ENNReal.ofReal (x ^ h * y ^ m / (1 - x * y)) := by
  have hsum :=
    RhinViola.weightedGeometricKernelHasSum h m x y hx hy hxy
  have hnonneg : ∀ k : ℕ, 0 ≤ x ^ (h + k) * y ^ (m + k) := by
    intro k
    exact mul_nonneg (pow_nonneg hx _) (pow_nonneg hy _)
  calc
    (∑' k : ℕ,
        ENNReal.ofReal (x ^ (h + k)) *
          ENNReal.ofReal (y ^ (m + k))) =
      ∑' k : ℕ,
        ENNReal.ofReal (x ^ (h + k) * y ^ (m + k)) := by
          apply tsum_congr
          intro k
          rw [ENNReal.ofReal_mul (pow_nonneg hx _)]
    _ = ENNReal.ofReal
        (∑' k : ℕ, x ^ (h + k) * y ^ (m + k)) := by
          exact (ENNReal.ofReal_tsum_of_nonneg hnonneg hsum.summable).symm
    _ = ENNReal.ofReal (x ^ h * y ^ m / (1 - x * y)) := by
          rw [hsum.tsum_eq]
