-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_061
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:12:04.071718+00:00
-- url     : https://prove2.me/submissions/b4505a93-c79e-4d05-811c-e630d10de67e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_061
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 33, witnessCheck (witnessD7_061 j) = true ∧ (witnessD7_061 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
