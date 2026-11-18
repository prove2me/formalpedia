-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_086
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:19:49.925285+00:00
-- url     : https://prove2.me/submissions/18b993dc-60ec-4240-a0ba-766361cebdc0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_086
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD8_086 j) = true ∧ (witnessD8_086 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
