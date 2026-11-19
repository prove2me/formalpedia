-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_126
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:12:41.914424+00:00
-- url     : https://prove2.me/submissions/16dca61b-e3dc-42c3-843c-6c5a7b6b20be

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_126
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessP9_126 j) = true ∧ (witnessP9_126 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
