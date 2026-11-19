-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_082
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:07:49.193203+00:00
-- url     : https://prove2.me/submissions/177d49a9-43af-408a-8272-66bd31773a6e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_082
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessP9_082 j) = true ∧ (witnessP9_082 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
