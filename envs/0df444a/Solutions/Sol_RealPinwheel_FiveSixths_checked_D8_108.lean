-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_108
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:38:34.864775+00:00
-- url     : https://prove2.me/submissions/413f5e5f-09fb-489f-a1de-94e400d6c2c9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_108
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessD8_108 j) = true ∧ (witnessD8_108 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
