-- Prove2me | solution 2 for Riemann_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-20T22:36:24.678172+00:00
-- url     : https://prove2.me/submissions/18d3bea5-39f0-41e7-8a42-7d23657d9cba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlpoGeChallenge_LFunction_eq_zero_re_of_isPrimitive

theorem solution :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := by
  intro s h0 h1 hz
  exact AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive 1 1
    DirichletCharacter.isPrimitive_one_level_one s h0 h1
    (by rw [DirichletCharacter.LFunction_modOne_eq]; exact hz)
