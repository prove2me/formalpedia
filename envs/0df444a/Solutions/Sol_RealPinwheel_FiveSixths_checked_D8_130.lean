-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_130
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:55:19.11709+00:00
-- url     : https://prove2.me/submissions/e71c6fb3-a8fe-4f4e-bf71-a4c71dbff6af

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_130
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessD8_130 j) = true ∧ (witnessD8_130 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
