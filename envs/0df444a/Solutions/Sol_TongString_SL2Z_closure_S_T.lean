-- Prove2me | solution 1 for TongString.SL2Z_closure_S_T
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T22:02:15.510361+00:00
-- url     : https://prove2.me/submissions/d96d2bbe-ed5c-45d5-b1b3-0d7ae37dd636

import Mathlib
import Definitions.Def_TongString_modular_action

open TongString

theorem solution : Subgroup.closure {modularS, modularT} = ⊤ := by
  have hS : modularS = ModularGroup.S := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hT : modularT = ModularGroup.T := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hS, hT]
  exact SpecialLinearGroup.SL2Z_generators
