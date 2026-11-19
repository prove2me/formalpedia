-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_212
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:50:21.866775+00:00
-- url     : https://prove2.me/submissions/b7fd5979-19ed-4a8c-b389-3600dbd6f459

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_212
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessP9_212 j) = true ∧ (witnessP9_212 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
