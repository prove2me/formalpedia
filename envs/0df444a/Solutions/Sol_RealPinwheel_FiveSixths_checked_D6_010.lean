-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_010
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:39:04.594918+00:00
-- url     : https://prove2.me/submissions/cc945eae-be0f-4674-940f-6a87bb994c0b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_010
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 35, witnessCheck (witnessD6_010 j) = true ∧ (witnessD6_010 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
