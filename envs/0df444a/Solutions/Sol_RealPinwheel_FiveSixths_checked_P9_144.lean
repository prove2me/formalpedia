-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_144
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:40:04.957591+00:00
-- url     : https://prove2.me/submissions/92ab59f3-1979-4b7f-aaaf-053e9328f795

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_144
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessP9_144 j) = true ∧ (witnessP9_144 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
