-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_047
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:19:20.499469+00:00
-- url     : https://prove2.me/submissions/210b809d-a26f-4b69-98f0-246985108ed9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_047
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_047 j) = true ∧ (witnessP9_047 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
