-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_block_1e4_1e5
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T02:08:26.198031+00:00
-- url     : https://prove2.me/submissions/52ee9862-c8d1-42bc-a32e-0884df30ce51

import Mathlib
import Theorems.Thm_RHX100000_segment


theorem solution (s : ℂ) (hs : riemannZeta s = 0) (h0 : 0 < s.re)
    (h1 : s.re < 1) (ha : 10 ^ 4 ≤ s.im) (hb : s.im ≤ 10 ^ 5) : s.re = 1 / 2 := by
  exact RHX100000.segment s hs (by linarith) (by linarith [show (10 : ℝ) ^ 4 = 10000 by norm_num, show (10 : ℝ) ^ 5 = 100000 by norm_num]) (by linarith [show (10 : ℝ) ^ 5 = 100000 by norm_num, show (10 : ℝ) ^ 6 = 1000000 by norm_num])

