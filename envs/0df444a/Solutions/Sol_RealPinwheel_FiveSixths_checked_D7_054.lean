-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_054
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:00:57.722549+00:00
-- url     : https://prove2.me/submissions/88b5073a-9f05-46cf-a0d9-c0f69fd9a97c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_054
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 29, witnessCheck (witnessD7_054 j) = true ∧ (witnessD7_054 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
