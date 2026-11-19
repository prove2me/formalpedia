-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_219
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:41:50.224196+00:00
-- url     : https://prove2.me/submissions/e17b27d4-087b-422d-be91-3bd183df694a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_219
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 26, witnessCheck (witnessP9_219 j) = true ∧ (witnessP9_219 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
