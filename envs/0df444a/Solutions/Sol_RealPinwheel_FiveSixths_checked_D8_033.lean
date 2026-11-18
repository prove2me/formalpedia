-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_033
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:45:42.355447+00:00
-- url     : https://prove2.me/submissions/34492098-8dd6-4e6a-a2a4-4f7455b69f2d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_033
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessD8_033 j) = true ∧ (witnessD8_033 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
