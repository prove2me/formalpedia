-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_197
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:27:30.271722+00:00
-- url     : https://prove2.me/submissions/452294e5-b4c8-4f49-b7bf-b1cf97b08cfe

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_197
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessP9_197 j) = true ∧ (witnessP9_197 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
