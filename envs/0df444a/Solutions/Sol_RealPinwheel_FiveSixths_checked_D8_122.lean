-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_122
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:49:38.501338+00:00
-- url     : https://prove2.me/submissions/e74a86ae-766a-4f1c-8bb7-f04b0e08ddfe

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_122
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessD8_122 j) = true ∧ (witnessD8_122 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
