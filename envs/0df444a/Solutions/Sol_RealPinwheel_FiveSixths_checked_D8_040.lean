-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_040
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:50:26.459167+00:00
-- url     : https://prove2.me/submissions/d6536344-407c-4c43-b419-db98cc2ae34d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_040
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessD8_040 j) = true ∧ (witnessD8_040 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
