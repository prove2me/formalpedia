-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_313
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:40:39.120204+00:00
-- url     : https://prove2.me/submissions/418207a9-ea4b-4607-a45f-fde21d9caf3d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_313
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 59, witnessCheck (witnessP9_313 j) = true ∧ (witnessP9_313 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
