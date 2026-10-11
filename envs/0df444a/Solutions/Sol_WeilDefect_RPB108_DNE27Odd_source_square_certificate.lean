-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.source_square_certificate
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:18:03.824113+00:00
-- url     : https://prove2.me/submissions/d3d619e4-1a70-4f85-af65-558178bd79f5

import Definitions.Def_RPB108_DNE27Numerics_Odd
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Odd
theorem solution (i : Fin 4) :
    sourceSquare i ≤ (highFloor*(completedMass i-nativeMass i))^2 := by
  fin_cases i <;> norm_num [sourceSquare, highFloor, completedMass, nativeMass,
    scales, rawSourceSquare, rawCompletedMass, rawNativeMass]
