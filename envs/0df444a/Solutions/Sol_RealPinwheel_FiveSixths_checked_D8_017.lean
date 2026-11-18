-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_017
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:53:01.083099+00:00
-- url     : https://prove2.me/submissions/0aa549ea-e15f-44ed-a026-a24a718b3f91

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_017
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 4, witnessCheck (witnessD8_017 j) = true ∧ (witnessD8_017 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
