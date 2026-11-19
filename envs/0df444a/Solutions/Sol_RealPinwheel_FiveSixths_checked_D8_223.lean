-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_223
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:09:12.628441+00:00
-- url     : https://prove2.me/submissions/44e921e3-8086-4596-8be7-3d0661a57250

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_223
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessD8_223 j) = true ∧ (witnessD8_223 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
