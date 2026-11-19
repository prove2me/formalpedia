-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_187
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:36:29.04162+00:00
-- url     : https://prove2.me/submissions/b76bd8e6-2aa8-4f0c-bf40-93ce3b36e584

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_187
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 20, witnessCheck (witnessD8_187 j) = true ∧ (witnessD8_187 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
