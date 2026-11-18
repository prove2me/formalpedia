-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_121
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:47:06.500335+00:00
-- url     : https://prove2.me/submissions/c95a9983-7f78-468a-8455-c080e82744fc

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_121
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessD8_121 j) = true ∧ (witnessD8_121 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
