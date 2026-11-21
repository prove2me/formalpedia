-- Prove2me | solution 1 for TaoFivePrimes.rh_positive_121_to_67156_20261114
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-20T23:56:11.208934+00:00
-- url     : https://prove2.me/submissions/0a0027e2-7b21-4a11-9527-dae821014e18
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlpoGeChallenge_LFunction_eq_zero_re_of_isPrimitive

theorem solution (s : ℂ) (hz : riemannZeta s = 0)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hp : 0 < s.im)
    (ha : (121 : ℝ) ≤ s.im) (hb : s.im ≤ (67156 : ℝ) + 25 / 8192) :
    s.re = 1 / 2 :=
  AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive 1 1
    DirichletCharacter.isPrimitive_one_level_one s h0 h1
    (by rw [DirichletCharacter.LFunction_modOne_eq]; exact hz)
