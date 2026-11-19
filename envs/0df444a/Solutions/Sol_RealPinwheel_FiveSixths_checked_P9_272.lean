-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_272
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:15:20.230206+00:00
-- url     : https://prove2.me/submissions/f44913ea-cbd3-4352-a743-3764d4e68b68

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_272
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 38, witnessCheck (witnessP9_272 j) = true ∧ (witnessP9_272 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
