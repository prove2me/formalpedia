-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_026
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:59:23.10495+00:00
-- url     : https://prove2.me/submissions/4c4d0fd7-2d87-446b-9ddc-e38754fbb145

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_026
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 4, witnessCheck (witnessP9_026 j) = true ∧ (witnessP9_026 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
