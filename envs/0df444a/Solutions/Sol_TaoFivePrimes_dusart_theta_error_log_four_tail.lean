-- Prove2me | solution 1 for TaoFivePrimes.dusart_theta_error_log_four_tail
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-03T02:53:40.901168+00:00
-- url     : https://prove2.me/submissions/f9a68552-71a0-4b9b-8f6e-dd4d65076535
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_TaoFivePrimes_dusart_theta_exponential_error
import Theorems.Thm_TaoFivePrimes_dusart_envelope_log_four_comparison

theorem solution (x : ℝ)
    (hx : Real.exp 13900 ≤ x) :
    |Chebyshev.theta x - x| ≤
      (1513 / 10 : ℝ) * x / (Real.log x) ^ 4 := by
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have ht : 13900 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos 13900) hx
    simpa only [Real.log_exp] using hh
  have h := (TaoFivePrimes.dusart_theta_exponential_error x hx0 (by linarith)).le
  have hc := mul_le_mul_of_nonneg_left
    (TaoFivePrimes.dusart_envelope_log_four_comparison (Real.log x) ht) hx0.le
  calc
    _ ≤ x * (Real.sqrt (8 / Real.pi) *
        Real.sqrt (Real.sqrt (Real.log x / (569693 / 100000 : ℝ))) *
        Real.exp (-Real.sqrt (Real.log x / (569693 / 100000 : ℝ)))) := by
      simpa only [mul_assoc] using h
    _ ≤ x * ((1513 / 10 : ℝ) / (Real.log x)^4) := hc
    _ = _ := by ring
