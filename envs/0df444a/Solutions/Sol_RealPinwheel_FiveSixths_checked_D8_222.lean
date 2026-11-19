-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_222
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:10:14.875885+00:00
-- url     : https://prove2.me/submissions/f6075173-c48c-4158-8178-1a6750d6d51d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_222
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessD8_222 j) = true ∧ (witnessD8_222 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
