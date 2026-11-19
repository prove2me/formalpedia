-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_226
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:57:47.491202+00:00
-- url     : https://prove2.me/submissions/c19b08be-6c0b-4a56-a21d-a4c0ff675c04

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_226
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessP9_226 j) = true ∧ (witnessP9_226 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
