-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_209
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:58:17.459756+00:00
-- url     : https://prove2.me/submissions/e62f113a-13d1-4bc4-8be9-e35f9f24e1af

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_209
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessD8_209 j) = true ∧ (witnessD8_209 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
