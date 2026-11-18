-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_066
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:23:40.095317+00:00
-- url     : https://prove2.me/submissions/61c12a69-d87f-4396-89fd-55041e3f0e30

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_066
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 40, witnessCheck (witnessD7_066 j) = true ∧ (witnessD7_066 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
