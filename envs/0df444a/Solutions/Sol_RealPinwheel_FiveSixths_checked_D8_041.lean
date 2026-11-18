-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_041
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:48:35.319628+00:00
-- url     : https://prove2.me/submissions/26a6cf50-b2f4-4f63-8ef3-146d35ca5feb

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_041
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessD8_041 j) = true ∧ (witnessD8_041 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
