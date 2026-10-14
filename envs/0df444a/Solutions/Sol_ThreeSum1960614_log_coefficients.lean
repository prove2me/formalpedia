-- Prove2me | solution 1 for ThreeSum1960614.log_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:19:43.952965+00:00
-- url     : https://prove2.me/submissions/9d2086b1-71ae-4420-852e-01a1d1811742

import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1000
open scoped BigOperators

private noncomputable def logSeries (n : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * i + 1)

private theorem log_bounds_of_atanh {y z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hy : (1 + z) / (1 - z) = y) (n : ℕ) :
    2 * logSeries n z ≤ Real.log y ∧
      Real.log y ≤ 2 * (logSeries n z + z ^ (2 * n + 1) / (1 - z ^ 2)) := by
  have hlo := Real.sum_range_le_log_div hz0 hz1 n
  have hhi := Real.log_div_le_sum_range_add hz0 hz1 n
  constructor
  · calc
      2 * logSeries n z ≤ Real.log ((1 + z) / (1 - z)) := by
        simpa [logSeries, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
          (mul_le_mul_of_nonneg_left hlo (by norm_num : 0 ≤ (2 : ℝ)))
      _ = Real.log y := by rw [hy]
  · calc
      Real.log y = Real.log ((1 + z) / (1 - z)) := by rw [hy]
      _ ≤ 2 * (logSeries n z + z ^ (2 * n + 1) / (1 - z ^ 2)) := by
        have hm := mul_le_mul_of_nonneg_left hhi (by norm_num : 0 ≤ (2 : ℝ))
        calc
          Real.log ((1 + z) / (1 - z)) =
              2 * (1 / 2 * Real.log ((1 + z) / (1 - z))) := by ring
          _ ≤ 2 * (logSeries n z + z ^ (2 * n + 1) / (1 - z ^ 2)) := by
            simpa [logSeries] using hm

private theorem log_two_bounds :
    (693147180559945 / 10^15 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ 693147180559946 / 10^15 := by
  have h := log_bounds_of_atanh (y := 2) (z := (1 : ℝ) / 3)
    (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · have hs : (693147180559945 / 10^15 : ℝ) ≤
        2 * logSeries 16 ((1 : ℝ) / 3) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 16 ((1 : ℝ) / 3) +
        ((1 : ℝ) / 3) ^ (2 * 16 + 1) / (1 - ((1 : ℝ) / 3) ^ 2)) ≤
          693147180559946 / 10^15 := by norm_num [logSeries]
    exact h.2.trans hs

theorem solution :
    (693147180559945 / 10^15 : ℝ) ≤ Real.log 2 ∧
    Real.log 2 ≤ (693147180559946 / 10^15 : ℝ) ∧
    (785174904 / 100000000 : ℝ) * Real.log 2 < Real.log 231 ∧
    (2 * 72447023 / 100000000 : ℝ) * Real.log 2 ≤ 1 + (1 / 231 : ℝ) ∧
    (3 * 24044466 / 100000000 : ℝ) * Real.log 2 ≤ (1 - (1 / 231 : ℝ) ^ 2) / 2 ∧
    (4 * 12022459 / 100000000 : ℝ) * Real.log 2 ≤ (1 + (1 / 231 : ℝ) ^ 3) / 3 := by
  obtain ⟨hl, hu⟩ := log_two_bounds
  refine ⟨hl, hu, ?_, ?_, ?_, ?_⟩
  · have h := (log_bounds_of_atanh (y := (231 : ℝ) / 128) (z := (103 : ℝ) / 359)
      (by norm_num) (by norm_num) (by norm_num) 16).1
    have hs : ((785174904 / 100000000 : ℝ) - 7) * (693147180559946 / 10^15) <
        2 * logSeries 16 ((103 : ℝ) / 359) := by norm_num [logSeries]
    have h128 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
      have hpow := Real.log_pow (2 : ℝ) 7
      norm_num at hpow
      exact hpow
    rw [Real.log_div (by norm_num : (231 : ℝ) ≠ 0) (by norm_num : (128 : ℝ) ≠ 0), h128] at h
    nlinarith
  · nlinarith [show (2 * 72447023 / 100000000 : ℝ) * (693147180559946 / 10^15) ≤
        1 + (1 / 231 : ℝ) by norm_num]
  · nlinarith [show (3 * 24044466 / 100000000 : ℝ) * (693147180559946 / 10^15) ≤
        (1 - (1 / 231 : ℝ) ^ 2) / 2 by norm_num]
  · nlinarith [show (4 * 12022459 / 100000000 : ℝ) * (693147180559946 / 10^15) ≤
        (1 + (1 / 231 : ℝ) ^ 3) / 3 by norm_num]

#print axioms solution
