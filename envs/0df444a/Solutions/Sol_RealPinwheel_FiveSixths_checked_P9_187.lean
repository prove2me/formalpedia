-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_187
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:13:57.249063+00:00
-- url     : https://prove2.me/submissions/23b69b35-ea53-4b01-b1f7-fd39b5e1e355

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_187
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 20, witnessCheck (witnessP9_187 j) = true ∧ (witnessP9_187 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
