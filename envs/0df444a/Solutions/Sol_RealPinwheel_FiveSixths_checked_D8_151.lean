-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_151
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:13:21.63909+00:00
-- url     : https://prove2.me/submissions/5d2ef712-0f19-4e3c-b1a3-67acef2e1a42

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_151
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessD8_151 j) = true ∧ (witnessD8_151 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
