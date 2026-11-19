-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_128
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:54:37.838888+00:00
-- url     : https://prove2.me/submissions/53770f06-d356-4bc6-b5c7-a273bc68a6c0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_128
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessD8_128 j) = true ∧ (witnessD8_128 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
