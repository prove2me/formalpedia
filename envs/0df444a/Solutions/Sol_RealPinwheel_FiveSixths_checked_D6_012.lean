-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_012
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:40:04.655194+00:00
-- url     : https://prove2.me/submissions/72b30d12-59e7-4e68-926b-a34ac199b61f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_012
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 43, witnessCheck (witnessD6_012 j) = true ∧ (witnessD6_012 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
