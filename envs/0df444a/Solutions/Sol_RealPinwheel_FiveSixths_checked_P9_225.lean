-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_225
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:52:24.382209+00:00
-- url     : https://prove2.me/submissions/9cef2cd3-5f23-4da5-b177-362b61e08677

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_225
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessP9_225 j) = true ∧ (witnessP9_225 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
