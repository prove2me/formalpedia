-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_093
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:21:51.622639+00:00
-- url     : https://prove2.me/submissions/84ad8ca2-a8f1-4105-b34d-d6fecedcd0d9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_093
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD8_093 j) = true ∧ (witnessD8_093 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
