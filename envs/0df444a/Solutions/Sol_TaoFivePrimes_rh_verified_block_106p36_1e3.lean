-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_block_106p36_1e3
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:53:01.012429+00:00
-- url     : https://prove2.me/submissions/18e55a78-452e-40fb-9404-7cb6c0839bc1

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_106_107
import Theorems.Thm_TaoFivePrimes_rh_verified_block_107_1e3

set_option autoImplicit false
open Complex TaoFivePrimes

theorem solution (s : ℂ) (hs : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (ha : (2659/25:ℝ) ≤ s.im)
    (hb : s.im ≤ 10^3) : s.re = 1/2 := by
  rcases le_or_gt s.im 107 with h | h
  · have h106 : (106:ℝ) ≤ s.im := by linarith
    exact (zeta_zero_free_rectangle_106_107 s h0 h1 h106 h hs).elim
  · exact rh_verified_block_107_1e3 s hs h0 h1 h.le hb
