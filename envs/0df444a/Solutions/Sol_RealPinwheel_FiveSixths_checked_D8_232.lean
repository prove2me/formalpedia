-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_232
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:18:48.315868+00:00
-- url     : https://prove2.me/submissions/8a985b0d-e96b-4e26-9c67-78d9e05ec79c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_232
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 31, witnessCheck (witnessD8_232 j) = true ∧ (witnessD8_232 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
