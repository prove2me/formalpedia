-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_306
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:37:06.781204+00:00
-- url     : https://prove2.me/submissions/53deef14-39b4-45bb-96d4-f719941ff801

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_306
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 53, witnessCheck (witnessP9_306 j) = true ∧ (witnessP9_306 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
