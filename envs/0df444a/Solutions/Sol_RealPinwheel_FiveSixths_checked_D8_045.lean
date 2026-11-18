-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_045
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:58:07.353531+00:00
-- url     : https://prove2.me/submissions/ceb2c1ae-da7a-4daf-a009-702dcaa98c35

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_045
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessD8_045 j) = true ∧ (witnessD8_045 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
