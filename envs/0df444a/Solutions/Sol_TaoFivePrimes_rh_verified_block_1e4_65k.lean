-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_block_1e4_65k
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:52:32.171973+00:00
-- url     : https://prove2.me/submissions/8e6f56e2-161a-45f1-844c-e937dafa1d2f

import Theorems.Thm_H65K_Full121_segment

theorem solution (s : ℂ) (hs : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (ha : 10 ^ 4 ≤ s.im)
    (hb : s.im ≤ 65000) : s.re = 1 / 2 := by
  exact H65K.Full121.segment s hs (by linarith) (by linarith) hb
