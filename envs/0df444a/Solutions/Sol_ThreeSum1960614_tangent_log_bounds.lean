-- Prove2me | solution 1 for ThreeSum1960614.tangent_log_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:37:25.143299+00:00
-- url     : https://prove2.me/submissions/9f5769d8-6a63-4e46-8790-ac9974ca1a99

import Theorems.Thm_ThreeSum1960614_log_coefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
open scoped BigOperators
open ThreeSum1960614

private noncomputable def logSeries (n : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * i + 1)

private theorem log_lower {y z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hy : (1 + z) / (1 - z) = y) (n : ℕ) :
    2 * logSeries n z ≤ Real.log y := by
  calc
    2 * logSeries n z ≤ Real.log ((1 + z) / (1 - z)) := by
      simpa [logSeries, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
        (mul_le_mul_of_nonneg_left (Real.sum_range_le_log_div hz0 hz1 n)
          (by norm_num : 0 ≤ (2 : ℝ)))
    _ = Real.log y := by rw [hy]

theorem solution :
    -Real.log (1 - tangentPoint) / Real.log 2 < (272298515211 / 1000000000000 : ℝ) ∧
    (-Real.log (1 - tangentPoint) - Real.log tangentPoint) / (2 * Real.log 2) <
      (140590616299 / 100000000000 : ℝ) := by
  obtain ⟨_, hu, _, _, _, _⟩ := ThreeSum1960614.log_coefficients
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := log_lower (y := 2 * (1 - tangentPoint))
    (z := (32799931814908507 : ℝ) / 132799931814908507)
    (by norm_num) (by norm_num) (by norm_num [tangentPoint]) 16
  have h2 := log_lower (y := 8 * tangentPoint)
    (z := (4700068185091493 : ℝ) / 29700068185091493)
    (by norm_num) (by norm_num) (by norm_num [tangentPoint]) 16
  have hlog1 : Real.log (2 * (1 - tangentPoint)) =
      Real.log 2 + Real.log (1 - tangentPoint) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num [tangentPoint])]
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 3
    norm_num at h
    exact h
  have hlog2 : Real.log (8 * tangentPoint) =
      3 * Real.log 2 + Real.log tangentPoint := by
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (by norm_num [tangentPoint]), hlog8]
  rw [hlog1] at h1
  rw [hlog2] at h2
  constructor
  · have hs : (1 - (272298515211 / 1000000000000 : ℝ)) * (693147180559946 / 10^15) <
        2 * logSeries 16 ((32799931814908507 : ℝ) / 132799931814908507) := by
      norm_num [logSeries]
    have hprod := mul_le_mul_of_nonneg_left hu
      (by norm_num : (0 : ℝ) ≤ 1 - 272298515211 / 1000000000000)
    apply (div_lt_iff₀ hp).2
    linarith
  · have hs : (4 - 2 * (140590616299 / 100000000000 : ℝ)) * (693147180559946 / 10^15) <
        2 * logSeries 16 ((32799931814908507 : ℝ) / 132799931814908507) +
        2 * logSeries 16 ((4700068185091493 : ℝ) / 29700068185091493) := by
      norm_num [logSeries]
    have hprod := mul_le_mul_of_nonneg_left hu
      (by norm_num : (0 : ℝ) ≤ 4 - 2 * (140590616299 / 100000000000))
    apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.log 2)).2
    linarith
