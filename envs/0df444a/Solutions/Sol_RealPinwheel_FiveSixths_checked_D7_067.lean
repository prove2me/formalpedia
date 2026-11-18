-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_067
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:23:14.146744+00:00
-- url     : https://prove2.me/submissions/3629ecb0-9a6d-406f-aadd-403da0ab5dea

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_067
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 42, witnessCheck (witnessD7_067 j) = true ∧ (witnessD7_067 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
