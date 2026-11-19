-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_257
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:08:59.731899+00:00
-- url     : https://prove2.me/submissions/d349811b-920a-4277-823a-541053aa552d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_257
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 34, witnessCheck (witnessP9_257 j) = true ∧ (witnessP9_257 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
