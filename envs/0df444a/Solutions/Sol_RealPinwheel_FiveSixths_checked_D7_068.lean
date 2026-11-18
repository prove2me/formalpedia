-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_068
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:23:51.976269+00:00
-- url     : https://prove2.me/submissions/407a2c3c-9177-48e2-9fcc-39a9a073b128

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_068
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 46, witnessCheck (witnessD7_068 j) = true ∧ (witnessD7_068 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
