-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_179
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:33:21.035198+00:00
-- url     : https://prove2.me/submissions/c75ca9b3-f491-4d15-adf5-01ef04531f1b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_179
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessD8_179 j) = true ∧ (witnessD8_179 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
