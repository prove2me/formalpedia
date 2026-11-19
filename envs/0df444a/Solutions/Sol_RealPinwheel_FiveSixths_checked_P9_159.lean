-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_159
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:59:48.894545+00:00
-- url     : https://prove2.me/submissions/47ec44ac-10a9-4efc-b43d-14ace79ab964

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_159
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessP9_159 j) = true ∧ (witnessP9_159 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
