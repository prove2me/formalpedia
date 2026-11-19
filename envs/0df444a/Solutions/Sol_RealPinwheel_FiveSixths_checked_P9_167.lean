-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_167
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:00:41.796101+00:00
-- url     : https://prove2.me/submissions/7873ccf6-5c3f-4ab0-b682-2f2dc316db07

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_167
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessP9_167 j) = true ∧ (witnessP9_167 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
