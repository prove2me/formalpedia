-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_112
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:38:49.187369+00:00
-- url     : https://prove2.me/submissions/e1b6062a-d279-494a-b308-acc0d34d97b7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_112
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessD8_112 j) = true ∧ (witnessD8_112 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
