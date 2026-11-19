-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_229
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:17:33.105324+00:00
-- url     : https://prove2.me/submissions/e8c99738-c580-4861-b613-e25efb2e7cc6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_229
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 29, witnessCheck (witnessD8_229 j) = true ∧ (witnessD8_229 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
