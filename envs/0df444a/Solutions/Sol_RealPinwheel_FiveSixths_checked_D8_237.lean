-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_237
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:26:34.013866+00:00
-- url     : https://prove2.me/submissions/5ffc7cbb-ff76-4221-a0ca-be9376da6878

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_237
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 34, witnessCheck (witnessD8_237 j) = true ∧ (witnessD8_237 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
