-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_184
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:03:08.282065+00:00
-- url     : https://prove2.me/submissions/764b912a-e663-4773-992e-5f801971e4d9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_184
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 20, witnessCheck (witnessP9_184 j) = true ∧ (witnessP9_184 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
