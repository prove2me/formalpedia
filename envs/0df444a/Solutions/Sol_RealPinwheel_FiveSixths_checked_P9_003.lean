-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_003
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:36:45.751095+00:00
-- url     : https://prove2.me/submissions/d3005d84-ac43-43c6-8250-1594614917e5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_003
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 1, witnessCheck (witnessP9_003 j) = true ∧ (witnessP9_003 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
