-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_316
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:43:02.814443+00:00
-- url     : https://prove2.me/submissions/ef27bada-a765-4737-9edf-81911e1a6139

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_316
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 62, witnessCheck (witnessP9_316 j) = true ∧ (witnessP9_316 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
