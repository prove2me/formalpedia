-- Prove2me | solution 3 for TaoFivePrimes.rh_verified_block_135_1e3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:42:18.147996+00:00
-- url     : https://prove2.me/submissions/02bc2dba-9102-4460-8041-40f178fbc21c

import Mathlib
import Theorems.Thm_TaoFivePrimes_rh_verified_block_1e2_1e3

namespace TaoFivePrimes
end TaoFivePrimes
open TaoFivePrimes

theorem solution (s : ℂ) (hs : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (ha : (135:ℝ) ≤ s.im)
    (hb : s.im ≤ 10^3) : s.re = 1/2 :=
  TaoFivePrimes.rh_verified_block_1e2_1e3 s hs h0 h1 (by norm_num; linarith) hb
