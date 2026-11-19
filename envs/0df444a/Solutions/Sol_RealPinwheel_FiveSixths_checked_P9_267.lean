-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_267
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:14:31.107931+00:00
-- url     : https://prove2.me/submissions/447c7c2e-8937-46de-94ad-956f944224fe

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_267
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 37, witnessCheck (witnessP9_267 j) = true ∧ (witnessP9_267 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
