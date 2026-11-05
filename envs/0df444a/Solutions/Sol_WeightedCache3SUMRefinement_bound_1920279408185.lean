-- Prove2me | solution 1 for WeightedCache3SUMRefinement.bound_1920279408185
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:45:32.032033+00:00
-- url     : https://prove2.me/submissions/f072643a-3611-46dd-b4b9-14edfcd6a3b4

import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedRace_bound
import Mathlib.Tactic.NormNum

theorem solution : EndStatement.ThreeSum.SolvedInTime 1.920279408185 := by
  have h : (384055881637 / 200000000000 : Rat) = 1.920279408185 := by norm_num
  rw [← h]
  exact WeightedCache3SUMRefinement_e1ae71d.WeightedRace.bound
