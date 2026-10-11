-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.lower_pos
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:18:00.483888+00:00
-- url     : https://prove2.me/submissions/a9724c06-3e9a-4510-8ae4-3113b9897409

import Definitions.Def_RPB108_DNE27Numerics_Even
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Even
theorem solution (i : Fin 4) : 0 < lower i := by
  fin_cases i <;> norm_num [lower, lowLower, threeLower]
