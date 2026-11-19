-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_230
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:44:05.175952+00:00
-- url     : https://prove2.me/submissions/3adfe7c6-dd8d-42dd-a05f-02ab0b182e61

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_230
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 28, witnessCheck (witnessP9_230 j) = true ∧ (witnessP9_230 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
