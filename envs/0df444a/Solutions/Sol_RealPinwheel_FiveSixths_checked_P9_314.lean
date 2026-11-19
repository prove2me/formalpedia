-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_314
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:41:28.040956+00:00
-- url     : https://prove2.me/submissions/9f27b1fb-f083-429b-a6ba-fbf94a820271

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_314
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 62, witnessCheck (witnessP9_314 j) = true ∧ (witnessP9_314 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
