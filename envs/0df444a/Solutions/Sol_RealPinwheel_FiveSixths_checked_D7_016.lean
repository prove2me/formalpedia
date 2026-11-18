-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_016
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:25:51.181772+00:00
-- url     : https://prove2.me/submissions/8e4bf9ef-e98b-4019-b592-3a79a35ef9c9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_016
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessD7_016 j) = true ∧ (witnessD7_016 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
