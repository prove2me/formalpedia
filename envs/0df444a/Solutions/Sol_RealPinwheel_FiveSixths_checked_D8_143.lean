-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_143
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:09:14.632798+00:00
-- url     : https://prove2.me/submissions/4e6e593a-6d11-4709-9a34-ca3f83ca6ae4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_143
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessD8_143 j) = true ∧ (witnessD8_143 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
