-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_129
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:14:08.703946+00:00
-- url     : https://prove2.me/submissions/581ef4b8-da68-4001-81e1-642a4b261018

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_129
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessP9_129 j) = true ∧ (witnessP9_129 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
