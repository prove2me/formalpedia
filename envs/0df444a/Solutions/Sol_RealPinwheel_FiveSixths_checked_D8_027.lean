-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_027
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:41:59.074215+00:00
-- url     : https://prove2.me/submissions/689ceb32-2bb2-4e9f-8203-1a0f557bdd17

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_027
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessD8_027 j) = true ∧ (witnessD8_027 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
