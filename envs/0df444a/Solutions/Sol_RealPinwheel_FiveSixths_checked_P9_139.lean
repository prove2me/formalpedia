-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_139
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:32:10.568188+00:00
-- url     : https://prove2.me/submissions/3e3b2abd-9218-46a7-a9c3-f138181c3b77

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_139
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessP9_139 j) = true ∧ (witnessP9_139 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
