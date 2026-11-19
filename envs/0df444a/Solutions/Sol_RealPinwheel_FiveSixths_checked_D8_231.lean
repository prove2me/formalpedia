-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_231
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:19:54.298651+00:00
-- url     : https://prove2.me/submissions/ba8a64a6-5d03-4b34-b4cb-f0f6b767c967

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_231
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 31, witnessCheck (witnessD8_231 j) = true ∧ (witnessD8_231 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
