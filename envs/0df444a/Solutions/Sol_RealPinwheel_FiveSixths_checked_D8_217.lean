-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_217
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:05:27.3802+00:00
-- url     : https://prove2.me/submissions/38772038-f7bc-48ac-961c-5a8ff1849162

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_217
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 26, witnessCheck (witnessD8_217 j) = true ∧ (witnessD8_217 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
