-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_142
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:06:29.894965+00:00
-- url     : https://prove2.me/submissions/a9f64e4d-3974-4e82-aeb4-cefa3613f743

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_142
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessD8_142 j) = true ∧ (witnessD8_142 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
