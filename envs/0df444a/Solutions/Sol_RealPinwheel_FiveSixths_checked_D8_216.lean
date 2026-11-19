-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_216
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:11:40.733876+00:00
-- url     : https://prove2.me/submissions/b63f437b-12bb-4649-bf03-30b5b963ff1a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_216
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 26, witnessCheck (witnessD8_216 j) = true ∧ (witnessD8_216 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
