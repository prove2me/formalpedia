-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_240
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:29:08.711794+00:00
-- url     : https://prove2.me/submissions/981fbf59-7e0d-4fbb-b764-c2cc9c99a22a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_240
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 36, witnessCheck (witnessD8_240 j) = true ∧ (witnessD8_240 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
