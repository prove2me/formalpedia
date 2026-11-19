-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_186
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:19:14.188288+00:00
-- url     : https://prove2.me/submissions/47dc3b0b-5463-4d9e-a1c4-327c3da557a6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_186
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 20, witnessCheck (witnessP9_186 j) = true ∧ (witnessP9_186 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
