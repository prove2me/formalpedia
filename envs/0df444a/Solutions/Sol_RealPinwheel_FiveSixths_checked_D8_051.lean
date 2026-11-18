-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_051
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:54:06.176115+00:00
-- url     : https://prove2.me/submissions/0ad796b8-8810-4051-89e4-05642da7fd68

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_051
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessD8_051 j) = true ∧ (witnessD8_051 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
