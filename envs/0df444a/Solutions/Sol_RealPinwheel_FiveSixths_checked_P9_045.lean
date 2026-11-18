-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_045
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:18:42.31119+00:00
-- url     : https://prove2.me/submissions/e00badaa-69c5-481e-8a3f-64a5b09ca194

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_045
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_045 j) = true ∧ (witnessP9_045 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
