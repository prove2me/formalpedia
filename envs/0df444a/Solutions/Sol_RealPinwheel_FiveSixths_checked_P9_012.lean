-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_012
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:53:01.543353+00:00
-- url     : https://prove2.me/submissions/961f4a8a-1f3e-4206-aa49-b0a6bff65bfb

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_012
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 2, witnessCheck (witnessP9_012 j) = true ∧ (witnessP9_012 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
