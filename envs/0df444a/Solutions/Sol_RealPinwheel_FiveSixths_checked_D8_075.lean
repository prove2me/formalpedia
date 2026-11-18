-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_075
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:09:12.052419+00:00
-- url     : https://prove2.me/submissions/7081380d-26fa-4f54-b530-2924f91fa3ef

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_075
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessD8_075 j) = true ∧ (witnessD8_075 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
