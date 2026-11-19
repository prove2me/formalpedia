-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_143
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:41:10.987202+00:00
-- url     : https://prove2.me/submissions/cf3dfb2a-f90d-4c07-ba6b-926046c6844b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_143
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessP9_143 j) = true ∧ (witnessP9_143 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
