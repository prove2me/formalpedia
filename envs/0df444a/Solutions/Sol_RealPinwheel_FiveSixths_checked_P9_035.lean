-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_035
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:03:17.199219+00:00
-- url     : https://prove2.me/submissions/370e03b1-ddc1-4aa1-a89b-499084e207b2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_035
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_035 j) = true ∧ (witnessP9_035 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
