-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_108
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:47:58.558912+00:00
-- url     : https://prove2.me/submissions/5582a786-b195-4196-934d-9b40c2fff9e3

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_108
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessP9_108 j) = true ∧ (witnessP9_108 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
