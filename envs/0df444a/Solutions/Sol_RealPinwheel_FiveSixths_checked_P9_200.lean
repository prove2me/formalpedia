-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_200
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:42:02.335203+00:00
-- url     : https://prove2.me/submissions/49c2c9f0-5102-47c3-890f-5032b325dd8a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_200
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessP9_200 j) = true ∧ (witnessP9_200 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
