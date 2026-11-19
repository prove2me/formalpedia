-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_241
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:29:58.949834+00:00
-- url     : https://prove2.me/submissions/86e02c39-caeb-4e3c-85e4-0a11e645e746

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_241
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 38, witnessCheck (witnessD8_241 j) = true ∧ (witnessD8_241 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
