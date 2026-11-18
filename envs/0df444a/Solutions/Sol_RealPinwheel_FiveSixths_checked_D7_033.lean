-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_033
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:44:24.757223+00:00
-- url     : https://prove2.me/submissions/b008ccb1-ec21-4b50-b32d-8ed5d4a140fe

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_033
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessD7_033 j) = true ∧ (witnessD7_033 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
