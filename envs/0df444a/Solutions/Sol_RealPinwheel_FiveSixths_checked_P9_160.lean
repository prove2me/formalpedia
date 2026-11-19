-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_160
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:03:30.443461+00:00
-- url     : https://prove2.me/submissions/0eb89c05-913e-400a-8905-a9138dc57e45

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_160
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessP9_160 j) = true ∧ (witnessP9_160 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
