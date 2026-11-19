-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_074
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:00:59.94081+00:00
-- url     : https://prove2.me/submissions/22400a70-416e-4aea-911d-bf64493a8d1b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_074
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessP9_074 j) = true ∧ (witnessP9_074 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
