-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_053
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:23:23.907222+00:00
-- url     : https://prove2.me/submissions/d7de5907-f088-4b30-8964-87e8f8b55f74

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_053
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessP9_053 j) = true ∧ (witnessP9_053 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
