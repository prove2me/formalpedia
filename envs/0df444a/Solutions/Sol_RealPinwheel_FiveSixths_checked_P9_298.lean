-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_298
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:30:42.884098+00:00
-- url     : https://prove2.me/submissions/1399a2e9-6c4e-45d9-a14b-301f5880bb66

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_298
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 50, witnessCheck (witnessP9_298 j) = true ∧ (witnessP9_298 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
