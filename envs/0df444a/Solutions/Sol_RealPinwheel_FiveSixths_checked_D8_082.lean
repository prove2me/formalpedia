-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_082
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:14:43.259144+00:00
-- url     : https://prove2.me/submissions/edff8579-f388-4eb4-9b20-0cb789a94054

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_082
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD8_082 j) = true ∧ (witnessD8_082 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
