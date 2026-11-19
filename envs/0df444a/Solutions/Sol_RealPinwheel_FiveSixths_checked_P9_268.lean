-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_268
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:14:59.465016+00:00
-- url     : https://prove2.me/submissions/1e5a31d0-ff35-48a6-b817-dfe366ff8166

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_268
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 37, witnessCheck (witnessP9_268 j) = true ∧ (witnessP9_268 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
