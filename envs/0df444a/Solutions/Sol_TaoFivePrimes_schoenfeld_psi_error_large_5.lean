-- Prove2me | solution 5 for TaoFivePrimes.schoenfeld_psi_error_large
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:19:07.176917+00:00
-- url     : https://prove2.me/submissions/5d50b4c7-460e-4e04-8998-b5603571a460
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_to_exp23
import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_middle_of_rh_100k
import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_above_exp136
import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_two
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e2_1e3
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e3_1e4
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e4_1e5

set_option autoImplicit false
open Complex TaoFivePrimes

private lemma rh_up_to_100k (s : ℂ) (hz : riemannZeta s = 0) (h0 : 0 < s.re)
    (h1 : s.re < 1) (him : 0 ≤ s.im) (hT : s.im ≤ 10 ^ 5) : s.re = 1 / 2 := by
  have h2 : 2 < s.im := by
    by_contra h
    exact zeta_ne_zero_of_mem_strip_of_abs_im_le_two s h0 h1
      (by rw [abs_of_nonneg him]; linarith) hz
  rcases le_or_gt s.im 14 with h | h
  · exact absurd hz (zeta_ne_zero_strip_im_two_to_fourteen s h0 h1 h2.le h)
  rcases le_or_gt s.im (10 ^ 2) with h' | h'
  · exact rh_verified_block_14_1e2 s hz h0 h1 h.le h'
  rcases le_or_gt s.im (10 ^ 3) with h | h
  · exact rh_verified_block_1e2_1e3 s hz h0 h1 h'.le h
  rcases le_or_gt s.im (10 ^ 4) with h' | h'
  · exact rh_verified_block_1e3_1e4 s hz h0 h1 h.le h'
  exact rh_verified_block_1e4_1e5 s hz h0 h1 h'.le hT

theorem solution (y : ℝ) (hy : 10 ^ 8 ≤ y) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by
  by_cases hsmall : y < Real.exp 23
  · exact schoenfeld_psi_error_to_exp23 y hy hsmall
  by_cases hlarge : Real.exp 136 ≤ y
  · exact schoenfeld_psi_error_above_exp136 y hlarge
  · exact schoenfeld_psi_error_middle_of_rh_100k
      rh_up_to_100k y (le_of_not_gt hsmall) (lt_of_not_ge hlarge)
