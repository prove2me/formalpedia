-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.lower_pos
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:18:02.597311+00:00
-- url     : https://prove2.me/submissions/cab51b95-6e33-4e20-a9b8-96cd07700107

import Definitions.Def_RPB108_DNE27Numerics_Odd
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Odd
theorem solution (i : Fin 4) : 0 < lower i := by
  fin_cases i <;> norm_num [lower, lowLower, threeLower]
