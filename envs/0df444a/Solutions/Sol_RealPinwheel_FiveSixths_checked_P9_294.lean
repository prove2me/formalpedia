-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_294
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:27:48.668496+00:00
-- url     : https://prove2.me/submissions/4926aa02-a462-4fc9-8ea2-465d107ebc11

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_294
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 46, witnessCheck (witnessP9_294 j) = true ∧ (witnessP9_294 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
