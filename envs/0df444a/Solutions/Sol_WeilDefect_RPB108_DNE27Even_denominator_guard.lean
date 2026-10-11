-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.denominator_guard
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:18:01.995997+00:00
-- url     : https://prove2.me/submissions/f55b82fb-dc7e-452b-a46a-b21943d7c45a

import Definitions.Def_RPB108_DNE27Numerics_Even
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Even
theorem solution :
    gap * ((∑ i, (completedMass i)^2/lower i)+1/highFloor) ≤ 1 := by
  norm_num [gap, highFloor, completedMass, scales, rawCompletedMass,
    lower, lowLower, threeLower, Fin.sum_univ_succ]
