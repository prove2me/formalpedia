-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_235
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:24:47.006328+00:00
-- url     : https://prove2.me/submissions/a1b7a218-9cff-4c86-81d6-b470a34a66e2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_235
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 33, witnessCheck (witnessD8_235 j) = true ∧ (witnessD8_235 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
