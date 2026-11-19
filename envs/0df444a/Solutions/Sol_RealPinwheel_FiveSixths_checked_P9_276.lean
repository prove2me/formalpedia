-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_276
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:16:39.927317+00:00
-- url     : https://prove2.me/submissions/c9d85bf0-99f5-4ac5-a919-7ef6edfb7794

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_276
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 39, witnessCheck (witnessP9_276 j) = true ∧ (witnessP9_276 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
