-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_222
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:42:31.349202+00:00
-- url     : https://prove2.me/submissions/479f2bc1-d667-4b6e-86c8-428180b09c10

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_222
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 26, witnessCheck (witnessP9_222 j) = true ∧ (witnessP9_222 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
