-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_010
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:22:03.249743+00:00
-- url     : https://prove2.me/submissions/c1756fe9-c9c1-4636-9eaa-cf492255d566

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_010
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD7_010 j) = true ∧ (witnessD7_010 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
