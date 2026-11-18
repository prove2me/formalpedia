-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_040
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:48:32.176292+00:00
-- url     : https://prove2.me/submissions/fde80b57-895b-46fc-9496-05f9eeba104b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_040
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessD7_040 j) = true ∧ (witnessD7_040 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
