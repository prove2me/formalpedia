-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_323
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:46:14.288267+00:00
-- url     : https://prove2.me/submissions/ca228a6b-c009-422e-8c1a-0d18ce3383bc

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_323
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 75, witnessCheck (witnessP9_323 j) = true ∧ (witnessP9_323 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
