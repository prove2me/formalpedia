-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_147
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:42:04.302272+00:00
-- url     : https://prove2.me/submissions/a699be60-7478-4fb3-8bce-54f34850a660

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_147
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessP9_147 j) = true ∧ (witnessP9_147 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
