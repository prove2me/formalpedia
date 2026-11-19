-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_197
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:45:09.980725+00:00
-- url     : https://prove2.me/submissions/326945b9-cb4b-4951-b198-060963763cfb

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_197
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessD8_197 j) = true ∧ (witnessD8_197 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
