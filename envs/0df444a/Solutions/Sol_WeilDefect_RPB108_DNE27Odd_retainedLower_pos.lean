-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.retainedLower_pos
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:18:07.825672+00:00
-- url     : https://prove2.me/submissions/5e743ba1-bb28-451d-a67e-7dc5c9b2966d

import Definitions.Def_RPB108_DNE27MixedEnergy_Odd
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Odd
theorem solution : 0 < retainedLower := by norm_num [retainedLower]
