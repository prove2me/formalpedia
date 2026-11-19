-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_209
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:52:48.764183+00:00
-- url     : https://prove2.me/submissions/a509985f-c4a8-4cbe-a53d-4557faf6d2c6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_209
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessP9_209 j) = true ∧ (witnessP9_209 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
