-- Prove2me | solution 2 for connes_spectral_rh
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:33:28.90575+00:00
-- url     : https://prove2.me/submissions/43f3b019-e319-45fb-9af2-bda666766f73
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line



theorem solution :
    ∀ s : ℂ, s.re > 0 → s.re < 1 → riemannZeta s = 0 → s.re = 1/2 :=
  fun s h0 h1 hz => riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis s hz h0 h1
