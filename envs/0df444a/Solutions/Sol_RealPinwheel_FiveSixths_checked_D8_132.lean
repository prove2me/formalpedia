-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_132
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:56:10.497885+00:00
-- url     : https://prove2.me/submissions/eda31dec-a5b2-4334-8fd4-ddec68ab5d2e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_132
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessD8_132 j) = true ∧ (witnessD8_132 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
