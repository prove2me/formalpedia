-- Prove2me | solution 1 for TaoFivePrimes.dusart_table1_psi_bounds_for_log_four
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-11-13T21:40:52.822817+00:00
-- url     : https://prove2.me/submissions/939fcae1-ded8-4197-8f9c-261acef9b2de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_dusart_table1_psi_bounds_for_log_four_from_300
import Theorems.Thm_TaoFivePrimes_dusart_table1_psi_bounds_below_300_20261114
set_option autoImplicit false
noncomputable section

theorem solution
    (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (x : ℝ) (hx : Real.exp (r.b : ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x := by
  by_cases hb : 300 ≤ r.b
  · exact TaoFivePrimes.dusart_table1_psi_bounds_for_log_four_from_300 r hr hb x hx
  · exact TaoFivePrimes.dusart_table1_psi_bounds_below_300_20261114 r hr (Nat.lt_of_not_ge hb) x hx
