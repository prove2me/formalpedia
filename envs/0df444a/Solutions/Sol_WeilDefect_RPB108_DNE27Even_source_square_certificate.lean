-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.source_square_certificate
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:18:45.423978+00:00
-- url     : https://prove2.me/submissions/36c604fa-c74a-4699-aa4c-4182c5dae637

import Definitions.Def_RPB108_DNE27Numerics_Even
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Even
theorem solution (i : Fin 4) :
    sourceSquare i ≤ (highFloor*(completedMass i-nativeMass i))^2 := by
  fin_cases i <;> norm_num [sourceSquare, highFloor, completedMass, nativeMass,
    scales, rawSourceSquare, rawCompletedMass, rawNativeMass]
