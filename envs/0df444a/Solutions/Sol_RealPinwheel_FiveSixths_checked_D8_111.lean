-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_111
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:39:51.816206+00:00
-- url     : https://prove2.me/submissions/4d5632d0-c69a-468c-96b9-0f5329b3c815

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_111
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessD8_111 j) = true ∧ (witnessD8_111 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
