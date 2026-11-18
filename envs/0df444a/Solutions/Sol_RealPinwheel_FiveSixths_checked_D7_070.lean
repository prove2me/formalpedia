-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_070
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:29:18.449116+00:00
-- url     : https://prove2.me/submissions/dc087c15-f9a6-41a2-918e-1b193c497262

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_070
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 53, witnessCheck (witnessD7_070 j) = true ∧ (witnessD7_070 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
