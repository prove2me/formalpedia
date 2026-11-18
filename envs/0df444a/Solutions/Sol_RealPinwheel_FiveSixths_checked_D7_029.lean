-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_029
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:42:56.598983+00:00
-- url     : https://prove2.me/submissions/c19e1a1d-6b79-4c28-866e-880d699987d0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_029
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 18, witnessCheck (witnessD7_029 j) = true ∧ (witnessD7_029 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
