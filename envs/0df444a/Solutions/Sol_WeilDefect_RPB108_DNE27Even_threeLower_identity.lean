-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.threeLower_identity
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:18:06.616525+00:00
-- url     : https://prove2.me/submissions/5605b2cf-665a-43f7-90a8-29efbd5dc371

import Definitions.Def_RPB108_DNE27MixedEnergy_Even
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Even
theorem solution : threeLower = theta*retainedLower := by
  norm_num [threeLower, theta, retainedLower]
