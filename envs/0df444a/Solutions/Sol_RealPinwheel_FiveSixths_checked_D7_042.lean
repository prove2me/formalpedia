-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_042
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:50:26.184248+00:00
-- url     : https://prove2.me/submissions/2d5ee5a3-eafb-4bf9-b2e7-9393073a31e2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_042
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessD7_042 j) = true ∧ (witnessD7_042 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
