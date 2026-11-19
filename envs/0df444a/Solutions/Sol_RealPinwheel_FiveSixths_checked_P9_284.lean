-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_284
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:23:44.390205+00:00
-- url     : https://prove2.me/submissions/25e2a6b8-b3ac-4069-a7ea-e4afae163720

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_284
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 43, witnessCheck (witnessP9_284 j) = true ∧ (witnessP9_284 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
