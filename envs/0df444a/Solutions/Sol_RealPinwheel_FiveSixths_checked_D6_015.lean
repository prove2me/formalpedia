-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_015
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:45:26.74129+00:00
-- url     : https://prove2.me/submissions/f2bc32eb-cc0a-4f66-8c79-301b3a36020d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_015
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 57, witnessCheck (witnessD6_015 j) = true ∧ (witnessD6_015 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
