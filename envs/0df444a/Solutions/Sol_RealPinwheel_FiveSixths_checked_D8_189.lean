-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_189
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:38:09.034161+00:00
-- url     : https://prove2.me/submissions/61802f7d-f710-49be-812f-7d088f530bec

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_189
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 20, witnessCheck (witnessD8_189 j) = true ∧ (witnessD8_189 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
