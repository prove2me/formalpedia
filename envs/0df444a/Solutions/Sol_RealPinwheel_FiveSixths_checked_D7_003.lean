-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_003
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:17:58.410685+00:00
-- url     : https://prove2.me/submissions/b9f40480-67ce-4478-9b5d-c2db915b839a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_003
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessD7_003 j) = true ∧ (witnessD7_003 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
