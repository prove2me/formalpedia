-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_179
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:09:36.925279+00:00
-- url     : https://prove2.me/submissions/92ac930b-063b-4c53-979e-d86d6baaafd9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_179
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessP9_179 j) = true ∧ (witnessP9_179 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
