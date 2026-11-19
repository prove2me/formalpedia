-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_282
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:21:13.192354+00:00
-- url     : https://prove2.me/submissions/e9832d66-6070-4c31-b2ba-ce4556f90bda

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_282
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 41, witnessCheck (witnessP9_282 j) = true ∧ (witnessP9_282 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
