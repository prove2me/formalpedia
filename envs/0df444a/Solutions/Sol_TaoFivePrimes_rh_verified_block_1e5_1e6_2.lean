-- Prove2me | solution 2 for TaoFivePrimes.rh_verified_block_1e5_1e6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:35:55.301907+00:00
-- url     : https://prove2.me/submissions/99b2d82b-a0f3-4898-b543-081d1c84b993
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line



namespace TaoFivePrimes
end TaoFivePrimes
open TaoFivePrimes
theorem solution (s : ℂ) (hs : riemannZeta s = 0) (h0 : 0 < s.re)
    (h1 : s.re < 1) (ha : 10 ^ 5 ≤ s.im) (hb : s.im ≤ 10 ^ 6) : s.re = 1 / 2 :=
  riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis s hs h0 h1
