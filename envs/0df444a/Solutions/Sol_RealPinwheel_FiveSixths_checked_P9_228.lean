-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_228
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:56:25.74567+00:00
-- url     : https://prove2.me/submissions/2f079c4a-8538-4a67-b6e0-9031dd527ddc

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_228
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessP9_228 j) = true ∧ (witnessP9_228 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
