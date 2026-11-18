-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_034
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:45:29.278009+00:00
-- url     : https://prove2.me/submissions/68449666-3f1b-41f9-8cba-c44c48aa0a03

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_034
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 20, witnessCheck (witnessD7_034 j) = true ∧ (witnessD7_034 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
