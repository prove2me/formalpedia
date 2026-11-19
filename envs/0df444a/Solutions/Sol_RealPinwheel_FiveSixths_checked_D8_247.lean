-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_247
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:33:26.235146+00:00
-- url     : https://prove2.me/submissions/bdd95ded-596c-4301-ac8e-d9f51450c884

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_247
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 57, witnessCheck (witnessD8_247 j) = true ∧ (witnessD8_247 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
