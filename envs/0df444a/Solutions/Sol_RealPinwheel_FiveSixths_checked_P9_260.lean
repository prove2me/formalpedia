-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_260
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:09:04.768217+00:00
-- url     : https://prove2.me/submissions/55e4f217-fd62-4882-b312-d2c446a211dd

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_260
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 35, witnessCheck (witnessP9_260 j) = true ∧ (witnessP9_260 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
