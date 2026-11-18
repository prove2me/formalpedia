-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_098
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:24:53.427186+00:00
-- url     : https://prove2.me/submissions/f91c479a-090a-4f74-bfb2-ee92b4b4687e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_098
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessD8_098 j) = true ∧ (witnessD8_098 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
