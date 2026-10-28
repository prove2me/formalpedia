-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_block_127p6_1e3
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:14:12.375515+00:00
-- url     : https://prove2.me/submissions/c00a6834-f0fc-4042-9564-c2b6f6094014

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_127p6_129p3
import Theorems.Thm_TaoFivePrimes_rh_verified_slice_129p3_129p8
import Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_129p8_130p4
import Theorems.Thm_TaoFivePrimes_rh_verified_block_130p4_1e3

set_option autoImplicit false
open Complex TaoFivePrimes

theorem solution (s : ℂ) (hs : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (ha : (638/5:ℝ) ≤ s.im)
    (hb : s.im ≤ 10^3) : s.re = 1/2 := by
  rcases le_or_gt s.im (1293/10:ℝ) with h0' | h0'
  · exact (zeta_zero_free_rectangle_127p6_129p3 s h0 h1 ha h0' hs).elim
  · rcases le_or_gt s.im (649/5:ℝ) with h1' | h1'
    · exact rh_verified_slice_129p3_129p8 s hs h0 h1 h0'.le h1'
    · rcases le_or_gt s.im (652/5:ℝ) with h2' | h2'
      · exact (zeta_zero_free_rectangle_129p8_130p4 s h0 h1 h1'.le h2' hs).elim
      · exact rh_verified_block_130p4_1e3 s hs h0 h1 h2'.le hb
