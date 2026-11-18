-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_012
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:25:37.311658+00:00
-- url     : https://prove2.me/submissions/fa8fcb76-8e02-43c4-8a34-5cc344f41e8e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_012
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 3, witnessCheck (witnessD8_012 j) = true ∧ (witnessD8_012 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
