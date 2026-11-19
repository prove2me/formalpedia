-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_291
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:26:33.691206+00:00
-- url     : https://prove2.me/submissions/a3e76f59-7ebf-4d97-8abe-de33859d91cc

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_291
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 46, witnessCheck (witnessP9_291 j) = true ∧ (witnessP9_291 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
