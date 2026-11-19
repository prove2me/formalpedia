-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_168
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:59:51.425611+00:00
-- url     : https://prove2.me/submissions/50443f7d-ef9f-4949-b0ed-bb546e816cc1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_168
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessP9_168 j) = true ∧ (witnessP9_168 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
