-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_041
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:17:14.421251+00:00
-- url     : https://prove2.me/submissions/92cc9768-dcc2-4ee3-b229-27353190868f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_041
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_041 j) = true ∧ (witnessP9_041 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
