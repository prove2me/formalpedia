-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_001
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:02:45.998469+00:00
-- url     : https://prove2.me/submissions/1f58c37c-f87f-4bef-9ce7-949d32925436

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_001
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessD6_001 j) = true ∧ (witnessD6_001 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
