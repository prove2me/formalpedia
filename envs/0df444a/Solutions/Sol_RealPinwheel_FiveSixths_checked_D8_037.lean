-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_037
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:48:03.570689+00:00
-- url     : https://prove2.me/submissions/544df2c0-4601-4f4b-9a57-b3da8ed8fb26

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_037
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessD8_037 j) = true ∧ (witnessD8_037 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
