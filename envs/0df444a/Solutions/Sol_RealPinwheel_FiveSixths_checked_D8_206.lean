-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_206
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:52:51.256089+00:00
-- url     : https://prove2.me/submissions/242577ca-100a-4426-ae49-205c4b53119f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_206
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 24, witnessCheck (witnessD8_206 j) = true ∧ (witnessD8_206 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
