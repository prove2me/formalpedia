-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_block_111p7_1e3
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:36:55.844946+00:00
-- url     : https://prove2.me/submissions/063b48b3-c606-4f4e-8c23-fe2220c58ba2

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_rh_verified_slice_111p7_112p1
import Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_112p1_112p9
import Theorems.Thm_TaoFivePrimes_rh_verified_block_112p9_1e3

set_option autoImplicit false
open Complex TaoFivePrimes

theorem solution (s : ℂ) (hs : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (ha : (1117/10:ℝ) ≤ s.im)
    (hb : s.im ≤ 10^3) : s.re = 1/2 := by
  rcases le_or_gt s.im (1121/10:ℝ) with h | h
  · exact rh_verified_slice_111p7_112p1 s hs h0 h1 ha h
  · rcases le_or_gt s.im (1129/10:ℝ) with h' | h'
    · exact (zeta_zero_free_rectangle_112p1_112p9 s h0 h1 h.le h' hs).elim
    · exact rh_verified_block_112p9_1e3 s hs h0 h1 h'.le hb
