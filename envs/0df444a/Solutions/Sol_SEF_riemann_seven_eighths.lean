-- Prove2me | solution 1 for SEF.riemann_seven_eighths
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:21:53.617159+00:00
-- url     : https://prove2.me/submissions/c33104b4-6242-48d0-8347-fafc85aac21d

import Mathlib
import Definitions.Def_SEF_theta
import Definitions.Def_SEF_hecke
import Theorems.Thm_OAI_riemannZeta_ne_zero_of_seven_eighths_lt_re

theorem solution
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0 :=
  OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs
