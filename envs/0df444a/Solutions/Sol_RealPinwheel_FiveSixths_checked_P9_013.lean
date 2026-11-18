-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_013
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:44:01.640642+00:00
-- url     : https://prove2.me/submissions/a34a96e1-3d66-4290-9db0-3e5b354bbc93

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_013
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 2, witnessCheck (witnessP9_013 j) = true ∧ (witnessP9_013 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
