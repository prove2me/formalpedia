-- Prove2me | solution 1 for TaoFivePrimes.dusart_theta_error_log_four
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Creamycream
-- created : 2026-09-29T14:14:49.243707+00:00
-- url     : https://prove2.me/submissions/2a2d7fed-4604-471d-b1d2-ebd709db6bf5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_dusart_theta_error_log_four_chebyshev

theorem solution (x : ℝ) (hx : 2 ≤ x) :
    |(∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ)) - x| ≤
      (1513 / 10 : ℝ) * x / (Real.log x) ^ 4 := by
  rw [← Chebyshev.theta_eq_sum_primesLE]
  exact TaoFivePrimes.dusart_theta_error_log_four_chebyshev x hx
