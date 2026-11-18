-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_018
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:37:17.10737+00:00
-- url     : https://prove2.me/submissions/a6c213cd-b996-46a0-ae31-87048e17ca71

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_018
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 4, witnessCheck (witnessD8_018 j) = true ∧ (witnessD8_018 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
