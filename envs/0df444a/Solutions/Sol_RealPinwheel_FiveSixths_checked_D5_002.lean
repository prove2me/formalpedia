-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D5_002
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:01:54.710178+00:00
-- url     : https://prove2.me/submissions/a7f51d09-c48b-43f8-82cf-50d8a4a06371

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD5_002
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 61, witnessCheck (witnessD5_002 j) = true ∧ (witnessD5_002 j).length ≤ 32 := by
  intro j
  fin_cases j <;> decide +kernel
