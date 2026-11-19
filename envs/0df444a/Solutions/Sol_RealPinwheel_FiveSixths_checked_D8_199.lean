-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_199
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:48:11.19642+00:00
-- url     : https://prove2.me/submissions/f8df81e7-51c7-452f-925c-a7a0bbb1745d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_199
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessD8_199 j) = true ∧ (witnessD8_199 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
