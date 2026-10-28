-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_block_1e3_1e4
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:52:31.492359+00:00
-- url     : https://prove2.me/submissions/03af9fca-8bce-4613-bbe9-31a5e7590665

import Theorems.Thm_H65K_Full121_segment

theorem solution (s : ℂ) (hs : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (ha : 10 ^ 3 ≤ s.im)
    (hb : s.im ≤ 10 ^ 4) : s.re = 1 / 2 := by
  exact H65K.Full121.segment s hs (by linarith) (by linarith) (by linarith)
