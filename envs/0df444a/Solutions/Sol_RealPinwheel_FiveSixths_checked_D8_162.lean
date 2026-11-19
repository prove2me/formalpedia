-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_162
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:24:28.399605+00:00
-- url     : https://prove2.me/submissions/65f0b344-005f-475b-aea2-40cf642d0fab

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_162
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessD8_162 j) = true ∧ (witnessD8_162 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
