-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_115
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:43:30.867235+00:00
-- url     : https://prove2.me/submissions/81636af6-0d22-4bf8-ad63-d8b79fbd8ee7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_115
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessD8_115 j) = true ∧ (witnessD8_115 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
