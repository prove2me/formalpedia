-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_114
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:40:39.655263+00:00
-- url     : https://prove2.me/submissions/f1db1e7d-1679-40f1-932b-0f5abc922b6b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_114
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessD8_114 j) = true ∧ (witnessD8_114 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
