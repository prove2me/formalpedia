-- Prove2me | solution 1 for PvsNP.P_ne_NP_of_NP_ne_coNP
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T06:26:57.902152+00:00
-- url     : https://prove2.me/submissions/23fec2de-ae5f-4123-9467-2b6af12120d3

import Theorems.Thm_PvsNP_coP_eq_P

open PvsNP

theorem solution (h : NP ≠ coNP) : P ≠ NP := by
  intro hPN
  refine h ?_
  have hco : coNP = { L : DecisionProblem | Lᶜ ∈ P } := by
    rw [hPN]
    rfl
  rw [hco, coP_eq_P, hPN]
