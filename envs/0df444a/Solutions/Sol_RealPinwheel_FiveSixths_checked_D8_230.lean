-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_230
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:17:48.471378+00:00
-- url     : https://prove2.me/submissions/d0dd75b9-f385-4f0a-acda-a7a3bbc43175

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_230
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 30, witnessCheck (witnessD8_230 j) = true ∧ (witnessD8_230 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
