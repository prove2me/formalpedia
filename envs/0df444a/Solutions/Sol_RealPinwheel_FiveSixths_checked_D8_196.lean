-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_196
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:44:03.759415+00:00
-- url     : https://prove2.me/submissions/494bbe48-94d5-46f7-bd1f-e8706cdeede1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_196
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessD8_196 j) = true ∧ (witnessD8_196 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
