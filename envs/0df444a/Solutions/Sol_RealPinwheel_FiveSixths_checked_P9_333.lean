-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_333
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:53:58.990911+00:00
-- url     : https://prove2.me/submissions/ed9638cd-4217-431b-b888-d63180d21840

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_333
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 105, witnessCheck (witnessP9_333 j) = true ∧ (witnessP9_333 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
