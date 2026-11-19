-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_124
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:12:07.264403+00:00
-- url     : https://prove2.me/submissions/babdbb85-0e14-4813-831f-e32a3bff7d07

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_124
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessP9_124 j) = true ∧ (witnessP9_124 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
