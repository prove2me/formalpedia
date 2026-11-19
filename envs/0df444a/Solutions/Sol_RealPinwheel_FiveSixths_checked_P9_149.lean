-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_149
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:49:18.168096+00:00
-- url     : https://prove2.me/submissions/9b44c914-be04-4745-a411-65fe6acd3c4d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_149
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessP9_149 j) = true ∧ (witnessP9_149 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
