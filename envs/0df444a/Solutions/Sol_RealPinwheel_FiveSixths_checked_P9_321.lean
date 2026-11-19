-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_321
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:44:31.837556+00:00
-- url     : https://prove2.me/submissions/19952ecc-d94b-45fb-8565-cc5b2f02aca1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_321
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 71, witnessCheck (witnessP9_321 j) = true ∧ (witnessP9_321 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
