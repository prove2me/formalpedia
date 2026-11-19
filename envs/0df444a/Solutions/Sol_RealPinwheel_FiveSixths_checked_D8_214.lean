-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_214
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:02:08.07554+00:00
-- url     : https://prove2.me/submissions/fce523ae-604a-43f8-af68-39addf693939

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_214
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 26, witnessCheck (witnessD8_214 j) = true ∧ (witnessD8_214 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
