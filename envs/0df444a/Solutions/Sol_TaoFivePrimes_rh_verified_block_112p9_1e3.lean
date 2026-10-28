-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_block_112p9_1e3
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:59:14.072437+00:00
-- url     : https://prove2.me/submissions/bb91f980-2699-4034-882b-ccb36feb142d

import Mathlib.Tactic
import Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_112p9_114p1
import Theorems.Thm_TaoFivePrimes_rh_verified_slice_114p1_114p6
import Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_114p6_116
import Theorems.Thm_TaoFivePrimes_rh_verified_slice_116_116p7
import Theorems.Thm_TaoFivePrimes_zeta_zero_free_rectangle_116p7_116p9
import Theorems.Thm_TaoFivePrimes_rh_verified_block_116p9_1e3

set_option autoImplicit false
open Complex TaoFivePrimes

theorem solution (s : ℂ) (hs : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (ha : (1129/10:ℝ) ≤ s.im)
    (hb : s.im ≤ 10^3) : s.re = 1/2 := by
  rcases le_or_gt s.im (1141/10:ℝ) with h0' | h0'
  · exact (zeta_zero_free_rectangle_112p9_114p1 s h0 h1 ha h0' hs).elim
  · rcases le_or_gt s.im (573/5:ℝ) with h1' | h1'
    · exact rh_verified_slice_114p1_114p6 s hs h0 h1 h0'.le h1'
    · rcases le_or_gt s.im (116:ℝ) with h2' | h2'
      · exact (zeta_zero_free_rectangle_114p6_116 s h0 h1 h1'.le h2' hs).elim
      · rcases le_or_gt s.im (1167/10:ℝ) with h3' | h3'
        · exact rh_verified_slice_116_116p7 s hs h0 h1 h2'.le h3'
        · rcases le_or_gt s.im (1169/10:ℝ) with h4' | h4'
          · exact (zeta_zero_free_rectangle_116p7_116p9 s h0 h1 h3'.le h4' hs).elim
          · exact rh_verified_block_116p9_1e3 s hs h0 h1 h4'.le hb
