-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_201
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:53:34.305201+00:00
-- url     : https://prove2.me/submissions/e8d96ef4-9da2-4408-9829-29bc2c7ac0cc

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_201
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessP9_201 j) = true ∧ (witnessP9_201 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
