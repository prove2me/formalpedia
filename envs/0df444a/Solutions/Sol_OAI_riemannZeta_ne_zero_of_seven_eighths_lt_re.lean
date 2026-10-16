-- Prove2me | solution 1 for OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-15T15:15:38.437632+00:00
-- url     : https://prove2.me/submissions/5e94a6e4-963d-4e50-aa12-1f4f8a27773b

import Theorems.Thm_OAI_DirichletCharacter_LFunction_ne_zero_of_seven_eighths_lt_re

/- Specialization of the mission's Dirichlet milestone to the unique character
modulo one, with Mathlib's assigned value at the pole handled separately. -/
theorem solution {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
    (1 : DirichletCharacter ℂ 1) hs (fun h => h1 h.2)
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h
