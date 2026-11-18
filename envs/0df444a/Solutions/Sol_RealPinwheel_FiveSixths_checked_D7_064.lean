-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_064
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:21:21.595784+00:00
-- url     : https://prove2.me/submissions/8fa62fa5-7e89-4a32-8647-63fbe42fe957

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_064
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 36, witnessCheck (witnessD7_064 j) = true ∧ (witnessD7_064 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
