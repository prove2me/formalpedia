-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_014
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:48:00.194886+00:00
-- url     : https://prove2.me/submissions/ceb1c7f7-1c3c-4279-a1ff-b470cf62d902

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_014
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 2, witnessCheck (witnessP9_014 j) = true ∧ (witnessP9_014 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
