-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_165
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:25:34.508417+00:00
-- url     : https://prove2.me/submissions/925fb95e-ed41-44cf-8767-1c3b42b4a1c0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_165
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessD8_165 j) = true ∧ (witnessD8_165 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
