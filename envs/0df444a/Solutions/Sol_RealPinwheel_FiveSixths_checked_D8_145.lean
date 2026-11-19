-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_145
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:10:38.858193+00:00
-- url     : https://prove2.me/submissions/efa71be0-562e-41d8-b34d-d30d2df48f98

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_145
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessD8_145 j) = true ∧ (witnessD8_145 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
