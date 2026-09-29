-- Prove2me | solution 1 for PvsNP.P_subset_coNP
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T06:26:58.391462+00:00
-- url     : https://prove2.me/submissions/ce541595-fe9f-43bf-a520-1d4f2ce79ae7

import Theorems.Thm_PvsNP_coP_eq_P
import Theorems.Thm_PvsNP_P_subset_NP_millennium

open PvsNP

theorem solution : P ⊆ coNP := by
  intro L hL
  rw [← coP_eq_P] at hL
  exact P_subset_NP_millennium hL
