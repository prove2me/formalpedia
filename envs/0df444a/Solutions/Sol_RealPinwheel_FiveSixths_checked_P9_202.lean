-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_202
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:39:20.970527+00:00
-- url     : https://prove2.me/submissions/7eb73d74-40ff-4390-b1d0-f5556d186b9a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_202
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessP9_202 j) = true ∧ (witnessP9_202 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
