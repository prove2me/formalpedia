-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_171
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:27:58.17391+00:00
-- url     : https://prove2.me/submissions/e303346d-e0f1-4ce7-8136-220780702a7a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_171
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 18, witnessCheck (witnessD8_171 j) = true ∧ (witnessD8_171 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
