-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_250
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:03:55.797905+00:00
-- url     : https://prove2.me/submissions/8d6fb7c8-fb4b-45e8-abad-7656f27065c6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_250
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 33, witnessCheck (witnessP9_250 j) = true ∧ (witnessP9_250 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
