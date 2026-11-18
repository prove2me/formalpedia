-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_048
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:21:48.56598+00:00
-- url     : https://prove2.me/submissions/e56f038d-0714-4ca4-b99b-da9101506881

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_048
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_048 j) = true ∧ (witnessP9_048 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
