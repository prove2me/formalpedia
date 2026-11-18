-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_050
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:58:36.934211+00:00
-- url     : https://prove2.me/submissions/e256cf79-3a86-44cc-af4a-e6aa9c4e6dc9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_050
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessD7_050 j) = true ∧ (witnessD7_050 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
