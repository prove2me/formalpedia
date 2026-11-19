-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_150
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:54:01.683092+00:00
-- url     : https://prove2.me/submissions/6bc3c60c-02a2-4aad-8fe9-3fe4947f8d91

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_150
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessP9_150 j) = true ∧ (witnessP9_150 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
