-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_113
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:49:28.092045+00:00
-- url     : https://prove2.me/submissions/e9f29b54-e9e7-4a28-905c-e17f3fd1b474

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_113
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessP9_113 j) = true ∧ (witnessP9_113 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
