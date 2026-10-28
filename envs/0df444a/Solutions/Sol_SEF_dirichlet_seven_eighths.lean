-- Prove2me | solution 1 for SEF.dirichlet_seven_eighths
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:21:45.674265+00:00
-- url     : https://prove2.me/submissions/086e1d9e-cf84-4bc6-907e-fa1d86c30196

import Mathlib
import Definitions.Def_SEF_theta
import Definitions.Def_SEF_hecke
import Theorems.Thm_OAI_DirichletCharacter_LFunction_ne_zero_of_seven_eighths_lt_re

open scoped _root_.DirichletCharacter

theorem solution
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hs hpole
