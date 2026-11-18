-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_051
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:58:53.130918+00:00
-- url     : https://prove2.me/submissions/4bdcefc4-65f8-429d-b35c-8987b8e3300b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_051
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessD7_051 j) = true ∧ (witnessD7_051 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
