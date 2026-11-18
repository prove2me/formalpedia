-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_083
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:16:24.416474+00:00
-- url     : https://prove2.me/submissions/cb1d9dad-aa9a-4d5d-9d64-d0bc30be6afc

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_083
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD8_083 j) = true ∧ (witnessD8_083 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
