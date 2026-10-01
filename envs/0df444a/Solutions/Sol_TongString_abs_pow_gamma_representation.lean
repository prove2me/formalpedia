-- Prove2me | solution 1 for TongString.abs_pow_gamma_representation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T18:53:49.416631+00:00
-- url     : https://prove2.me/submissions/c958d7a7-b74f-487e-a7e0-47ff42993aa1

import Mathlib

open Complex MeasureTheory in
theorem solution (r : ℝ) (hr : 0 < r) (a : ℂ) (ha : a.re < 1) :
    (r : ℂ) ^ (2 * a - 2) =
      1 / Gamma (1 - a) *
        ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (-a) * Complex.exp (-((r : ℂ) ^ 2 * t)) := by
  have h1 : 0 < (1 - a).re := by simp; linarith
  have hr2 : (0:ℝ) < r ^ 2 := by positivity
  have key := Complex.integral_cpow_mul_exp_neg_mul_Ioi h1 hr2
  have e1 : (1 - a) - 1 = -a := by ring
  rw [e1] at key
  have e2 : ((r ^ 2 : ℝ) : ℂ) = (r : ℂ) ^ 2 := by push_cast; ring
  rw [e2] at key
  rw [key]
  have hG : Gamma (1 - a) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos h1
  have hpow : (1 / (r : ℂ) ^ 2) ^ (1 - a) = (r : ℂ) ^ (2 * a - 2) := by
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hq : (1 / (r : ℂ) ^ 2) = ((1 / r ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have hq0 : (1 / (r : ℂ) ^ 2) ≠ 0 := by simp [hr0]
    rw [cpow_def_of_ne_zero hq0, cpow_def_of_ne_zero hr0, hq, ← Complex.ofReal_log (by positivity),
      ← Complex.ofReal_log hr.le]
    congr 1
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_pow]
    push_cast
    ring
  rw [hpow]
  field_simp
