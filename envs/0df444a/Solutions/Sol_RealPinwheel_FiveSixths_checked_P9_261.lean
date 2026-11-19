-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_261
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:09:19.811575+00:00
-- url     : https://prove2.me/submissions/58891327-84d0-4ca5-aad8-0b2ab5b8d65d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_261
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 35, witnessCheck (witnessP9_261 j) = true ∧ (witnessP9_261 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
