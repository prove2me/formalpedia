-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_005
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:17:46.460356+00:00
-- url     : https://prove2.me/submissions/863bc8f4-f76e-4668-b17e-2e2af182053b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_005
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessD7_005 j) = true ∧ (witnessD7_005 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
