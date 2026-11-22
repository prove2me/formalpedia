-- Prove2me | solution 8 for Riemann_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:33:27.09982+00:00
-- url     : https://prove2.me/submissions/129cc40e-a943-48f3-87e0-f2ba2da5ec21
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line



theorem solution :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 :=
  fun s h0 h1 hz => riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis s hz h0 h1
