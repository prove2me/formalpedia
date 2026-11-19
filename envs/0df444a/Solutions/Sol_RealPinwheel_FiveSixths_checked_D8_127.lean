-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_127
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:59:35.552435+00:00
-- url     : https://prove2.me/submissions/1f090ec7-65b0-4c40-a730-77dbeb616d4f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_127
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessD8_127 j) = true ∧ (witnessD8_127 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
