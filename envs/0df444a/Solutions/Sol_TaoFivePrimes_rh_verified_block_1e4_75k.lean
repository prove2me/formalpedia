-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_block_1e4_75k
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T02:08:30.277313+00:00
-- url     : https://prove2.me/submissions/5a3baca7-b104-4447-9f2b-30281e358a43

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Theorems.Thm_RHX100000_segment

theorem solution (s : ℂ)
    (hs : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : 10 ^ 4 ≤ s.im) (hb : s.im ≤ 75000) : s.re = 1 / 2 := by
  exact RHX100000.segment s hs (by linarith) (by linarith [show (10 : ℝ) ^ 4 = 10000 by norm_num, show (10 : ℝ) ^ 5 = 100000 by norm_num]) (by linarith [show (10 : ℝ) ^ 5 = 100000 by norm_num, show (10 : ℝ) ^ 6 = 1000000 by norm_num])
