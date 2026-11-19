-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_190
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:38:56.38297+00:00
-- url     : https://prove2.me/submissions/a234b389-5cdb-4d1a-b87c-51066a2316d8

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_190
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 20, witnessCheck (witnessD8_190 j) = true ∧ (witnessD8_190 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
