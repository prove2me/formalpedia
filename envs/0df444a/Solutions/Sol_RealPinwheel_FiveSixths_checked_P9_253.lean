-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_253
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:05:16.587876+00:00
-- url     : https://prove2.me/submissions/e6dda642-d310-4612-9f23-b31bdfc0d10f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_253
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 33, witnessCheck (witnessP9_253 j) = true ∧ (witnessP9_253 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
