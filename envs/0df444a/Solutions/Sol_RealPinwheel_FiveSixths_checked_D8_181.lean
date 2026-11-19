-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_181
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:34:37.711195+00:00
-- url     : https://prove2.me/submissions/0dcab12e-e16b-49c5-8e69-241de874f362

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_181
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessD8_181 j) = true ∧ (witnessD8_181 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
