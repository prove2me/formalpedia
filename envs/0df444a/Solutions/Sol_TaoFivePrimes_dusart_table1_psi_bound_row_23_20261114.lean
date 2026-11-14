-- Prove2me | solution 1 for TaoFivePrimes.dusart_table1_psi_bound_row_23_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-13T22:04:03.553771+00:00
-- url     : https://prove2.me/submissions/e8b012a3-b7e8-4df7-bdbd-dec61d4861d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_dusart_row23_low_zero_reciprocal_sum_20261114
import Theorems.Thm_TaoFivePrimes_dusart_row23_remaining_low_rh_20261114
import Theorems.Thm_TaoFivePrimes_dusart_row23_remaining_rh_tail_20261114
import Theorems.Thm_TaoFivePrimes_dusart_row23_conditional_67156_20261114
set_option autoImplicit false
noncomputable section

theorem solution (x : ℝ) (hx : Real.exp (23 : ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000 : ℝ)*x := by
  exact TaoFivePrimes.dusart_row23_conditional_67156_20261114
    TaoFivePrimes.dusart_row23_low_zero_reciprocal_sum_20261114
    TaoFivePrimes.dusart_row23_remaining_low_rh_20261114
    TaoFivePrimes.dusart_row23_remaining_rh_tail_20261114 x hx
