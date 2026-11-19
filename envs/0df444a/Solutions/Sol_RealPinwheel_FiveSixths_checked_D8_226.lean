-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_226
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:11:58.10088+00:00
-- url     : https://prove2.me/submissions/36ebb994-e29e-425a-8bc3-262e04a25291

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_226
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 29, witnessCheck (witnessD8_226 j) = true ∧ (witnessD8_226 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
