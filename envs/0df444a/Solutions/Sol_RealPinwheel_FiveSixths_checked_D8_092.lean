-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_092
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:21:51.59678+00:00
-- url     : https://prove2.me/submissions/cd5d9576-9567-4300-bf92-af1147040bf7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_092
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD8_092 j) = true ∧ (witnessD8_092 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
