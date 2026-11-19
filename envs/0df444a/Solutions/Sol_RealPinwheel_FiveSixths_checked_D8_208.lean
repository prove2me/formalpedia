-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_208
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:57:21.581454+00:00
-- url     : https://prove2.me/submissions/70941acb-226c-4aea-80e2-3b23fd7a349c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_208
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessD8_208 j) = true ∧ (witnessD8_208 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
