-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_block_133p2_1e3
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:52:30.817745+00:00
-- url     : https://prove2.me/submissions/f309dd98-c3b2-4bdb-bd5f-80d0e35e6f45

import Theorems.Thm_H65K_Full121_segment

theorem solution (s : ℂ) (hs : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (ha : (666 / 5 : ℝ) ≤ s.im)
    (hb : s.im ≤ 10 ^ 3) : s.re = 1 / 2 := by
  exact H65K.Full121.segment s hs (by linarith) (by linarith) (by linarith)
