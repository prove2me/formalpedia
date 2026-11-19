-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_218
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:07:34.36755+00:00
-- url     : https://prove2.me/submissions/39f53dee-8a9e-45ef-bf03-4915c79a80f8

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_218
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessD8_218 j) = true ∧ (witnessD8_218 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
