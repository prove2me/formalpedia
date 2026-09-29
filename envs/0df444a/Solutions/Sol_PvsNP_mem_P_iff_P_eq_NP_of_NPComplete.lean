-- Prove2me | solution 1 for PvsNP.mem_P_iff_P_eq_NP_of_NPComplete
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T06:32:24.288467+00:00
-- url     : https://prove2.me/submissions/3dc845ed-e735-4d06-a612-d2410d39668e

import Definitions.Def_PvsNP_reductions
import Theorems.Thm_PvsNP_mem_P_of_polyTimeReducible
import Theorems.Thm_PvsNP_P_subset_NP_millennium

open PvsNP

theorem solution (L : DecisionProblem) (hL : NPComplete L) :
    L ∈ P ↔ P = NP := by
  obtain ⟨hLNP, hHard⟩ := hL
  constructor
  · intro hLP
    refine Set.Subset.antisymm P_subset_NP_millennium ?_
    intro K hK
    exact mem_P_of_polyTimeReducible K L (hHard K hK) hLP
  · intro h
    rw [h]
    exact hLNP
