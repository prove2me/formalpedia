-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_151
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:56:13.245002+00:00
-- url     : https://prove2.me/submissions/5d4c627b-d32b-4cde-9d4a-5441f9a7d6fb

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_151
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessP9_151 j) = true ∧ (witnessP9_151 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
