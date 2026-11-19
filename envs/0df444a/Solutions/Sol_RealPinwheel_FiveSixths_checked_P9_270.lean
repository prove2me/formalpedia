-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_270
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:15:37.042689+00:00
-- url     : https://prove2.me/submissions/d1946d60-ebee-403e-acd7-59ccf86005ca

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_270
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 38, witnessCheck (witnessP9_270 j) = true ∧ (witnessP9_270 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
