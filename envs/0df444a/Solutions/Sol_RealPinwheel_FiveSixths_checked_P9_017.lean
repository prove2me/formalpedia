-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_017
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:46:46.417587+00:00
-- url     : https://prove2.me/submissions/331fbaff-29d1-427d-9b67-9cee5b450a24

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_017
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 2, witnessCheck (witnessP9_017 j) = true ∧ (witnessP9_017 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
