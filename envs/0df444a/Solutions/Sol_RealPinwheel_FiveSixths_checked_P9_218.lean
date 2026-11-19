-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_218
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:42:02.31751+00:00
-- url     : https://prove2.me/submissions/c47c87c7-4689-4834-86b8-200292099d97

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_218
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 26, witnessCheck (witnessP9_218 j) = true ∧ (witnessP9_218 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
