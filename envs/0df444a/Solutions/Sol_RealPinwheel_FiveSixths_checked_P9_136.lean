-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_136
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:32:58.226867+00:00
-- url     : https://prove2.me/submissions/4cb1dfab-2dc7-4ad6-9dc4-15361893683b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_136
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessP9_136 j) = true ∧ (witnessP9_136 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
