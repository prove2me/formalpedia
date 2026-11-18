-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_015
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:26:29.276214+00:00
-- url     : https://prove2.me/submissions/fd7ef12a-f359-4134-bc9b-e8faae8888d7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_015
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 4, witnessCheck (witnessD8_015 j) = true ∧ (witnessD8_015 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
