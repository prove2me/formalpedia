-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_134
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:19:27.934041+00:00
-- url     : https://prove2.me/submissions/a22ab22b-0d94-4dff-a5a6-3850add912b7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_134
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessP9_134 j) = true ∧ (witnessP9_134 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
