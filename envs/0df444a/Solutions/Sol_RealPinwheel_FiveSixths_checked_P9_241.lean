-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_241
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:54:22.516245+00:00
-- url     : https://prove2.me/submissions/8abd8f09-af22-4b8a-8f61-edc36523e4c1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_241
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 31, witnessCheck (witnessP9_241 j) = true ∧ (witnessP9_241 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
