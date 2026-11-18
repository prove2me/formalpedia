-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_094
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:22:46.19776+00:00
-- url     : https://prove2.me/submissions/63b2effa-0d4b-4ae9-858d-985335766815

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_094
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD8_094 j) = true ∧ (witnessD8_094 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
