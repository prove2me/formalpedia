-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.denominator_guard
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:18:04.413851+00:00
-- url     : https://prove2.me/submissions/c44f2bf0-450d-4bb9-b461-0aa8e4fc8212

import Definitions.Def_RPB108_DNE27Numerics_Odd
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Odd
theorem solution :
    gap * ((∑ i, (completedMass i)^2/lower i)+1/highFloor) ≤ 1 := by
  norm_num [gap, highFloor, completedMass, scales, rawCompletedMass,
    lower, lowLower, threeLower, Fin.sum_univ_succ]
