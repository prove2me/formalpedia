-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_028
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:59:26.994401+00:00
-- url     : https://prove2.me/submissions/e44ff8a0-0115-4462-b91b-7ecf57a3f5ea

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_028
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 4, witnessCheck (witnessP9_028 j) = true ∧ (witnessP9_028 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
