-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_239
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:29:11.562075+00:00
-- url     : https://prove2.me/submissions/2994e48a-a440-48b8-9929-1d1ec86f9c0d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_239
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 35, witnessCheck (witnessD8_239 j) = true ∧ (witnessD8_239 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
