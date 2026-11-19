-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_071
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:56:57.622255+00:00
-- url     : https://prove2.me/submissions/138428b1-9fdc-449a-93a0-629763440591

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_071
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessP9_071 j) = true ∧ (witnessP9_071 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
