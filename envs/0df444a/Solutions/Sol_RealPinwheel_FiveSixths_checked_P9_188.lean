-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_188
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:17:43.740228+00:00
-- url     : https://prove2.me/submissions/b9680dc0-3582-4270-adac-bee24b213df2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_188
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 20, witnessCheck (witnessP9_188 j) = true ∧ (witnessP9_188 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
