-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_152
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:59:53.301473+00:00
-- url     : https://prove2.me/submissions/0b230ea7-2914-4284-b4c0-0e76f04f1e0c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_152
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessP9_152 j) = true ∧ (witnessP9_152 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
