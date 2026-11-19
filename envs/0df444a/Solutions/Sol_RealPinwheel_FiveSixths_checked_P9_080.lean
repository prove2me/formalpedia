-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_080
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:06:28.598607+00:00
-- url     : https://prove2.me/submissions/9efcc34d-f542-4d2b-a079-1b2b46a4e692

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_080
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessP9_080 j) = true ∧ (witnessP9_080 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
