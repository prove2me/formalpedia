-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_044
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:18:04.402552+00:00
-- url     : https://prove2.me/submissions/36aefb0d-fefb-4c7e-a242-0664b4171308

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_044
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_044 j) = true ∧ (witnessP9_044 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
