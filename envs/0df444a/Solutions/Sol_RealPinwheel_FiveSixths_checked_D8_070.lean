-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_070
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:06:54.833305+00:00
-- url     : https://prove2.me/submissions/6b367c61-61a3-4e13-b3b0-1d74e28083cb

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_070
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessD8_070 j) = true ∧ (witnessD8_070 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
