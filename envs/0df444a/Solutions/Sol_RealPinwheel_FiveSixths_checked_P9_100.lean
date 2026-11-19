-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_100
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:31:38.69927+00:00
-- url     : https://prove2.me/submissions/032c8162-7564-43d8-a5fb-446acb5880d0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_100
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessP9_100 j) = true ∧ (witnessP9_100 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
