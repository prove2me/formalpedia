-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_213
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:35:11.919597+00:00
-- url     : https://prove2.me/submissions/73e27c2a-fa45-4e88-b9ac-f70624921660

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_213
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessP9_213 j) = true ∧ (witnessP9_213 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
