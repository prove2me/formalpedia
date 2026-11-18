-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_043
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:54:54.099637+00:00
-- url     : https://prove2.me/submissions/d526dbe6-4a8f-47aa-b622-4a80fac510ef

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_043
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessD8_043 j) = true ∧ (witnessD8_043 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
