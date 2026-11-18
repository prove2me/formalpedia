-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_020
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:27:42.129673+00:00
-- url     : https://prove2.me/submissions/79fe2e64-e0ff-44d5-85e0-9b70908f5c1b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_020
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessD7_020 j) = true ∧ (witnessD7_020 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
