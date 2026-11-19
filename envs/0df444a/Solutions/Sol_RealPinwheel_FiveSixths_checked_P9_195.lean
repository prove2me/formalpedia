-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_195
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:18:48.568946+00:00
-- url     : https://prove2.me/submissions/bc574f93-761f-438d-a65f-b340b3e996ea

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_195
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessP9_195 j) = true ∧ (witnessP9_195 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
