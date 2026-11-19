-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_238
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:47:59.805782+00:00
-- url     : https://prove2.me/submissions/47fc9d5c-bfcf-480f-9970-963573d876e1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_238
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 29, witnessCheck (witnessP9_238 j) = true ∧ (witnessP9_238 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
