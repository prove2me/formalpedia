-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.threeLower_identity
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:18:08.249976+00:00
-- url     : https://prove2.me/submissions/93c30c1c-cb13-44d6-b84b-a9506d7bd251

import Definitions.Def_RPB108_DNE27MixedEnergy_Odd
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Odd
theorem solution : threeLower = theta*retainedLower := by
  norm_num [threeLower, theta, retainedLower]
