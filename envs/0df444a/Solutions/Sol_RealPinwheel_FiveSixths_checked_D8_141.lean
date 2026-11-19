-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_141
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:04:39.471581+00:00
-- url     : https://prove2.me/submissions/092f8aba-794c-4e06-9679-8ec0d73459ba

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_141
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessD8_141 j) = true ∧ (witnessD8_141 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
