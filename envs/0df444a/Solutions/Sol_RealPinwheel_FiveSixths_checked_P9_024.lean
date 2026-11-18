-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_024
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:56:43.924197+00:00
-- url     : https://prove2.me/submissions/ece6ae1c-7311-4936-9eb7-3c628bec2848

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_024
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 3, witnessCheck (witnessP9_024 j) = true ∧ (witnessP9_024 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
