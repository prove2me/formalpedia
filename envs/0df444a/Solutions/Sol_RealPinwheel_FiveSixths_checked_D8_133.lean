-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_133
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:58:28.269702+00:00
-- url     : https://prove2.me/submissions/fd234c93-2f75-440f-85c4-937b9c9db6d2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_133
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessD8_133 j) = true ∧ (witnessD8_133 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
