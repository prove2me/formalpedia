-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_064
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:04:47.238497+00:00
-- url     : https://prove2.me/submissions/c81d0ad4-30ea-420a-b7a9-808e0ec14860

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_064
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessD8_064 j) = true ∧ (witnessD8_064 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
