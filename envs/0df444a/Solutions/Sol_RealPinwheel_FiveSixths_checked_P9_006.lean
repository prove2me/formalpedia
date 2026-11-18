-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_006
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:36:24.48334+00:00
-- url     : https://prove2.me/submissions/2fb41a49-c2f8-47bf-95c9-fa5b667dd651

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_006
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 1, witnessCheck (witnessP9_006 j) = true ∧ (witnessP9_006 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
