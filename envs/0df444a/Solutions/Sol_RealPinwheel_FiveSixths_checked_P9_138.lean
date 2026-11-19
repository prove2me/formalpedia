-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_138
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:32:20.61148+00:00
-- url     : https://prove2.me/submissions/242230b6-f272-4caf-96a7-04846413e226

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_138
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessP9_138 j) = true ∧ (witnessP9_138 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
