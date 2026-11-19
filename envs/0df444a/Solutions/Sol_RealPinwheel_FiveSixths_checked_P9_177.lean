-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_177
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:01:27.592762+00:00
-- url     : https://prove2.me/submissions/168c013e-9fb9-417a-a800-7f4293b34458

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_177
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessP9_177 j) = true ∧ (witnessP9_177 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
