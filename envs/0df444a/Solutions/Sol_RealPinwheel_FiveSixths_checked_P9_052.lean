-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_052
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:22:24.445907+00:00
-- url     : https://prove2.me/submissions/1754d539-965a-46a8-b838-1ede6c8123d7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_052
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessP9_052 j) = true ∧ (witnessP9_052 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
