-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_052
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:58:45.870005+00:00
-- url     : https://prove2.me/submissions/d1affe81-7d26-4533-ac0e-d012577d77ba

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_052
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessD7_052 j) = true ∧ (witnessD7_052 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
