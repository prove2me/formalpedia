-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_182
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:34:45.170718+00:00
-- url     : https://prove2.me/submissions/35adf17a-62d7-43ed-915f-2a80dce54bee

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_182
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessD8_182 j) = true ∧ (witnessD8_182 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
