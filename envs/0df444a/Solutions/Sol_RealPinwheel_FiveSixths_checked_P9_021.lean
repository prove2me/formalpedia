-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_021
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:50:13.266207+00:00
-- url     : https://prove2.me/submissions/38ed39c2-f3b7-4d2e-8264-ef4db9eed422

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_021
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 3, witnessCheck (witnessP9_021 j) = true ∧ (witnessP9_021 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
