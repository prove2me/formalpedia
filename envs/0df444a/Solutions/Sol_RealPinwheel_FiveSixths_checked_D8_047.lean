-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_047
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:55:35.219762+00:00
-- url     : https://prove2.me/submissions/024a416d-4e53-44f7-9bd7-24e35bcb7cd1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_047
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessD8_047 j) = true ∧ (witnessD8_047 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
