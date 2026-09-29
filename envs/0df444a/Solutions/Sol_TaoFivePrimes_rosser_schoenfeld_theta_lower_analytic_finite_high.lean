-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_finite_high
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T14:14:32.717903+00:00
-- url     : https://prove2.me/submissions/7d2b7fe8-15b5-4fd2-ae55-8d01db400c42

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large

open TaoFivePrimes

theorem solution (t : Real) (h1 : 10 ^ 6 <= t) (h2 : t <= 10 ^ 8) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by
  have htpos : 0 < t := by norm_num at h1 ⊢; linarith
  have hgt1 : 1 < t := by norm_num at h1 ⊢; linarith
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
  have hlogpos : 0 < Real.log t := Real.log_pos hgt1
  have qpos : 0 < t ^ (1 / 4 : Real) := Real.rpow_pos_of_pos htpos _
  have hq4 : (t ^ (1 / 4 : Real)) ^ 4 = t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul htpos.le]
    norm_num
  have hqgt16 : (16 : Real) < t ^ (1 / 4 : Real) := by
    by_contra h
    have hqle : t ^ (1 / 4 : Real) <= 16 := le_of_not_gt h
    have hpow : (t ^ (1 / 4 : Real)) ^ 4 <= (16 : Real) ^ 4 := by gcongr
    rw [hq4] at hpow
    norm_num at hpow
    norm_num at h1
    linarith
  have hsqrteq : (t ^ (1 / 4 : Real)) ^ 2 = Real.sqrt t := by
    have hsqrtsq := Real.sq_sqrt (le_of_lt htpos)
    nlinarith [hq4]
  have hlogsmall : 4 * Real.log t < Real.sqrt t := by
    have hb := Real.log_le_rpow_div (le_of_lt htpos) (by norm_num : (0 : Real) < 1 / 4)
    have hb' : Real.log t <= 4 * t ^ (1 / 4 : Real) := by
      norm_num at hb ⊢
      linarith
    have hs : 16 * t ^ (1 / 4 : Real) < Real.sqrt t := by
      rw [← hsqrteq]
      nlinarith [qpos, hqgt16]
    nlinarith
  have hdiv : 2 * Real.sqrt t < t / (2 * Real.log t) := by
    apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.log t)).2
    have hmul := mul_lt_mul_of_pos_right hlogsmall hsqrt
    nlinarith [hmul]
  calc
    t * (1 - 1 / (2 * Real.log t)) = t - t / (2 * Real.log t) := by ring
    _ < t - 2 * Real.sqrt t := by linarith
    _ < Chebyshev.theta t := by
      apply rosser_schoenfeld_theta_lower_finite_large t
      · norm_num at h1 ⊢; linarith
      · exact h2
