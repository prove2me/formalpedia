-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_block_130p4_1e3
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:20:16.119023+00:00
-- url     : https://prove2.me/submissions/da2c422b-60d0-4268-b71b-748642a9d00c

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_130p4_130p8
import Theorems.Thm_TaoFivePrimes_rh_verified_slice_130p8_131p15
import Theorems.Thm_TaoFivePrimes_rh_verified_block_131p15_1e3

set_option autoImplicit false
open Complex TaoFivePrimes

theorem solution (s : ℂ) (hs : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (ha : (652/5:ℝ) ≤ s.im)
    (hb : s.im ≤ 10^3) : s.re = 1/2 := by
  rcases le_or_gt s.im (654/5:ℝ) with h0' | h0'
  · exact (zeta_zero_free_rectangle_130p4_130p8 s h0 h1 ha h0' hs).elim
  · rcases le_or_gt s.im (2623/20:ℝ) with h1' | h1'
    · exact rh_verified_slice_130p8_131p15 s hs h0 h1 h0'.le h1'
    · exact rh_verified_block_131p15_1e3 s hs h0 h1 h1'.le hb
