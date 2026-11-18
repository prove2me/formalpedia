-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_007
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:37:46.413514+00:00
-- url     : https://prove2.me/submissions/d0eee717-236b-4740-8450-154660cb8b13

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_007
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 1, witnessCheck (witnessP9_007 j) = true ∧ (witnessP9_007 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
