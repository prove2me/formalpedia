-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_163
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:26:02.283229+00:00
-- url     : https://prove2.me/submissions/2ea2095f-0768-4fd3-8019-68cb93487e82

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_163
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessD8_163 j) = true ∧ (witnessD8_163 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
