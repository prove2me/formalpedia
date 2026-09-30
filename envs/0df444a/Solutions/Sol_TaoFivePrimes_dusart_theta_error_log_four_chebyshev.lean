-- Prove2me | solution 1 for TaoFivePrimes.dusart_theta_error_log_four_chebyshev
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Creamycream
-- created : 2026-09-29T17:56:51.001595+00:00
-- url     : https://prove2.me/submissions/dad977df-b544-4ec5-bff5-248e28c9330e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_dusart_theta_error_log_four_table_range
import Theorems.Thm_TaoFivePrimes_dusart_theta_error_log_four_tail

theorem solution (x : ℝ) (hx : 2 ≤ x) :
    |Chebyshev.theta x - x| ≤
      (1513 / 10 : ℝ) * x / (Real.log x) ^ 4 := by
  rcases le_total x (Real.exp 13900) with htable | htail
  · exact TaoFivePrimes.dusart_theta_error_log_four_table_range x hx htable
  · exact TaoFivePrimes.dusart_theta_error_log_four_tail x htail
