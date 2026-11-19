-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_204
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:51:22.554722+00:00
-- url     : https://prove2.me/submissions/ecdbc9c9-b8a4-4b86-b59d-2095a524b86f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_204
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessD8_204 j) = true ∧ (witnessD8_204 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
