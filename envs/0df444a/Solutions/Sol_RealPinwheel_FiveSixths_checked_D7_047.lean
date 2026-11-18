-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_047
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:55:34.084199+00:00
-- url     : https://prove2.me/submissions/cf8e08ee-e1c3-4372-93c1-c8b35518ba5c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_047
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 26, witnessCheck (witnessD7_047 j) = true ∧ (witnessD7_047 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
