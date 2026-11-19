-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_219
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:04:14.932587+00:00
-- url     : https://prove2.me/submissions/662efe7f-070b-4c66-b592-18e5e7d517a5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_219
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessD8_219 j) = true ∧ (witnessD8_219 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
