-- Prove2me | solution 1 for TaoFivePrimes.rh_verified_block_1e6_1e7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-20T23:56:08.024817+00:00
-- url     : https://prove2.me/submissions/7951ae73-61e8-486a-a6a7-33e68dfd587f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlpoGeChallenge_LFunction_eq_zero_re_of_isPrimitive

theorem solution (s : ℂ) (hs : riemannZeta s = 0) (h0 : 0 < s.re)
    (h1 : s.re < 1) (ha : 10 ^ 6 ≤ s.im) (hb : s.im ≤ 10 ^ 7) : s.re = 1 / 2 :=
  AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive 1 1
    DirichletCharacter.isPrimitive_one_level_one s h0 h1
    (by rw [DirichletCharacter.LFunction_modOne_eq]; exact hs)
