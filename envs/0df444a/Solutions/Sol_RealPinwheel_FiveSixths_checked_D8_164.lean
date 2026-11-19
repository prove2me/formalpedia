-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_164
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:25:24.609486+00:00
-- url     : https://prove2.me/submissions/55376cfe-4081-405a-ba08-d9455fe22f18

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_164
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessD8_164 j) = true ∧ (witnessD8_164 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
