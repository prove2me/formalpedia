-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_004
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:13:22.956416+00:00
-- url     : https://prove2.me/submissions/bd505f23-c62c-47a0-bbdd-80a560227bc5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_004
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 26, witnessCheck (witnessD6_004 j) = true ∧ (witnessD6_004 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
