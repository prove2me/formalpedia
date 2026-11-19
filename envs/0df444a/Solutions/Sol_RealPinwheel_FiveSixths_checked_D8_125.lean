-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_125
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:56:00.036997+00:00
-- url     : https://prove2.me/submissions/217007ed-f169-4f8b-a006-942ee6c6fc31

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_125
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessD8_125 j) = true ∧ (witnessD8_125 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
