-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_165
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:10:11.26559+00:00
-- url     : https://prove2.me/submissions/b99cf389-1451-48c5-9739-eacd972d6551

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_165
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessP9_165 j) = true ∧ (witnessP9_165 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
