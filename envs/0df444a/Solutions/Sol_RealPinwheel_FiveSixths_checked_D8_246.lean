-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_246
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:33:50.815195+00:00
-- url     : https://prove2.me/submissions/cd88bbfd-5813-45f6-a052-b14e9fdd8079

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_246
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 51, witnessCheck (witnessD8_246 j) = true ∧ (witnessD8_246 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
