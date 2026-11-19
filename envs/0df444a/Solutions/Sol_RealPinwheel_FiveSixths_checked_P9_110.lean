-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_110
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:48:04.320993+00:00
-- url     : https://prove2.me/submissions/f267f7e4-e272-43f3-baaa-9fbf92d693a5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_110
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessP9_110 j) = true ∧ (witnessP9_110 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
