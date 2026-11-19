-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_081
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:05:18.781111+00:00
-- url     : https://prove2.me/submissions/ce8ffed0-8fa2-4bd6-a00a-366387c74830

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_081
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessP9_081 j) = true ∧ (witnessP9_081 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
