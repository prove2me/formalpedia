-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_block_127p2_1e3
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:56:41.654698+00:00
-- url     : https://prove2.me/submissions/83f579cd-846a-44ac-b507-9617e7ff6b30

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_rh_verified_slice_127p2_127p6
import Theorems.Thm_TaoFivePrimes_rh_verified_block_127p6_1e3

set_option autoImplicit false
open Complex TaoFivePrimes

theorem solution (s : ℂ) (hs : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (ha : (636/5:ℝ) ≤ s.im)
    (hb : s.im ≤ 10^3) : s.re = 1/2 := by
  rcases le_or_gt s.im (638/5:ℝ) with h | h
  · exact rh_verified_slice_127p2_127p6 s hs h0 h1 ha h
  · exact rh_verified_block_127p6_1e3 s hs h0 h1 h.le hb
