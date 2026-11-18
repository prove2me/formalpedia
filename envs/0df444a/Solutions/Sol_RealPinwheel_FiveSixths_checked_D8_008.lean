-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_008
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:36:19.021579+00:00
-- url     : https://prove2.me/submissions/46becdb3-edd4-4a67-85f7-a0cab03f9016

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_008
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 2, witnessCheck (witnessD8_008 j) = true ∧ (witnessD8_008 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
