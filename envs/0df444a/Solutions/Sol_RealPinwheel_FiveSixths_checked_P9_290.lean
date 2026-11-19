-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_290
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:26:43.965628+00:00
-- url     : https://prove2.me/submissions/417e64bc-01e2-4c30-801a-dd57b7987df4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_290
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 45, witnessCheck (witnessP9_290 j) = true ∧ (witnessP9_290 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
