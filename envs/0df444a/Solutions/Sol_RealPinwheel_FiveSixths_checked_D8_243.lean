-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_243
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:34:25.131734+00:00
-- url     : https://prove2.me/submissions/44716d4f-da09-4312-8729-6a9ea9bea481

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_243
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 41, witnessCheck (witnessD8_243 j) = true ∧ (witnessD8_243 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
