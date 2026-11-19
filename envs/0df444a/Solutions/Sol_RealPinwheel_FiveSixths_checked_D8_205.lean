-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_205
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:53:51.36319+00:00
-- url     : https://prove2.me/submissions/463434e9-07da-4765-88cf-d4ef5c0be58b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_205
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessD8_205 j) = true ∧ (witnessD8_205 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
