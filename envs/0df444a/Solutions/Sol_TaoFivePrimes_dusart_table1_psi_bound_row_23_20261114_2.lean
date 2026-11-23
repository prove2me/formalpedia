-- Prove2me | solution 2 for TaoFivePrimes.dusart_table1_psi_bound_row_23_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:07:22.962772+00:00
-- url     : https://prove2.me/submissions/d2dc8aea-3f3f-4929-bb9b-285cd7175bfb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Theorems.Thm_TaoFivePrimes_dusart_row23_low_zero_reciprocal_sum_20261114
import Theorems.Thm_TaoFivePrimes_dusart_row23_conditional_67156_20261114

namespace TaoFivePrimes
end TaoFivePrimes
open TaoFivePrimes

theorem solution
    (x : ℝ) (hx : Real.exp (23 : ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (2431/10000000 : ℝ)*x :=
  TaoFivePrimes.dusart_row23_conditional_67156_20261114
    TaoFivePrimes.dusart_row23_low_zero_reciprocal_sum_20261114
    (fun ρ _ =>
      riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis
        ρ.val ρ.property.1 ρ.property.2.1 ρ.property.2.2)
    (fun s hs _ _ =>
      riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis
        s hs.1 hs.2.1 hs.2.2)
    x hx
