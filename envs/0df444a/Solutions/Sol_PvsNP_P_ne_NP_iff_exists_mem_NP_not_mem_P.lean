-- Prove2me | solution 1 for PvsNP.P_ne_NP_iff_exists_mem_NP_not_mem_P
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T06:32:24.795004+00:00
-- url     : https://prove2.me/submissions/6fdc0c25-0a7d-475e-bf9d-b7dfe7f41042

import Theorems.Thm_PvsNP_P_subset_NP_millennium

open PvsNP

theorem solution :
    P ≠ NP ↔ ∃ L : DecisionProblem, L ∈ NP ∧ L ∉ P := by
  constructor
  · intro h
    by_contra hc
    refine h (Set.Subset.antisymm P_subset_NP_millennium ?_)
    intro K hK
    by_contra hKP
    exact hc ⟨K, hK, hKP⟩
  · rintro ⟨L, hNP, hP⟩ h
    exact hP (h ▸ hNP)
