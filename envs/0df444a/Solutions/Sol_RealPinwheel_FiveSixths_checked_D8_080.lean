-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_080
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:12:12.253204+00:00
-- url     : https://prove2.me/submissions/1befe80f-63ef-489a-9c99-ffc7b0470d30

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_080
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessD8_080 j) = true ∧ (witnessD8_080 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
