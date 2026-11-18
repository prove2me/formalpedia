-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_015
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:26:41.49996+00:00
-- url     : https://prove2.me/submissions/104bf616-08a7-4d95-ae0a-1f22d268604b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_015
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessD7_015 j) = true ∧ (witnessD7_015 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
