-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_236
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:50:50.328438+00:00
-- url     : https://prove2.me/submissions/363fc0a6-a5a0-424d-a436-0ff8f0d081aa

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_236
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 29, witnessCheck (witnessP9_236 j) = true ∧ (witnessP9_236 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
