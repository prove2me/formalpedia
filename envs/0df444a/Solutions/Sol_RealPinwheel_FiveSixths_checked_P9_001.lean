-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_001
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:41:49.857703+00:00
-- url     : https://prove2.me/submissions/06f01847-e549-4f54-a147-397351b77a9f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_001
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 1, witnessCheck (witnessP9_001 j) = true ∧ (witnessP9_001 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
