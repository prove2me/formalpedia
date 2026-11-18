-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_106
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:40:36.393299+00:00
-- url     : https://prove2.me/submissions/ce94ee5d-93d1-49e0-a2d6-874deb97e2f9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_106
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessD8_106 j) = true ∧ (witnessD8_106 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
