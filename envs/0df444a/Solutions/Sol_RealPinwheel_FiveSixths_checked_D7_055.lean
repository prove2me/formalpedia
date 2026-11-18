-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_055
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:06:40.290214+00:00
-- url     : https://prove2.me/submissions/36a81fe3-4363-4c15-91aa-e10ea0892ad4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_055
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 29, witnessCheck (witnessD7_055 j) = true ∧ (witnessD7_055 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
