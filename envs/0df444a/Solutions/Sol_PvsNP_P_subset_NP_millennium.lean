-- Prove2me | solution 1 for PvsNP.P_subset_NP_millennium
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T06:32:23.337631+00:00
-- url     : https://prove2.me/submissions/01aaad27-bd11-4f48-99f9-8078f8638b36

import Theorems.Thm_PvsNP_isPolyTime_comp
import Theorems.Thm_PvsNP_isPolyTime_fst

open PvsNP

theorem solution : P ⊆ NP := by
  intro L hL
  refine ⟨0, fun p => L p.1, ?_, ?_⟩
  · exact isPolyTime_comp Prod.fst L isPolyTime_fst hL
  · intro x
    constructor
    · intro h
      exact ⟨[], by simp, h⟩
    · rintro ⟨w, -, hw⟩
      exact hw
