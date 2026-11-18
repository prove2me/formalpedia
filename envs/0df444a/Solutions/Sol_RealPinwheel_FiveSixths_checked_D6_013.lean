-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_013
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:43:27.43779+00:00
-- url     : https://prove2.me/submissions/79412b75-5728-4bfd-af07-e8f6a8e48f71

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_013
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 48, witnessCheck (witnessD6_013 j) = true ∧ (witnessD6_013 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
