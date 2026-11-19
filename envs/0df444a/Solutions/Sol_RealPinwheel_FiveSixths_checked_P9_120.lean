-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_120
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:07:37.029675+00:00
-- url     : https://prove2.me/submissions/ce7e5174-2d0a-4c4f-a6e4-bd1c74e76bf9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_120
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessP9_120 j) = true ∧ (witnessP9_120 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
