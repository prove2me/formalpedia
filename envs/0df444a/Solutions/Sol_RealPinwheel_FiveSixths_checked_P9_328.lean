-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_328
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:51:45.25339+00:00
-- url     : https://prove2.me/submissions/9229f738-9fa5-4970-96a9-4ecd2db247c8

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_328
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 83, witnessCheck (witnessP9_328 j) = true ∧ (witnessP9_328 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
