-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_029
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:42:58.659205+00:00
-- url     : https://prove2.me/submissions/c3a3b8c4-3041-489f-b531-d1c9ba013aeb

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_029
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessD8_029 j) = true ∧ (witnessD8_029 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
