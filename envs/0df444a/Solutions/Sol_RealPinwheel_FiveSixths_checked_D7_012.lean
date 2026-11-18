-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_012
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:22:43.627767+00:00
-- url     : https://prove2.me/submissions/fad84686-537f-42bf-9c8a-e9132d7de078

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_012
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessD7_012 j) = true ∧ (witnessD7_012 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
