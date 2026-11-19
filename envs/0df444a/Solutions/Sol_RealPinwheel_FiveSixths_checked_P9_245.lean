-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_245
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:56:26.370529+00:00
-- url     : https://prove2.me/submissions/26685afb-9ba9-488d-b119-5da1fbefb174

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_245
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 31, witnessCheck (witnessP9_245 j) = true ∧ (witnessP9_245 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
