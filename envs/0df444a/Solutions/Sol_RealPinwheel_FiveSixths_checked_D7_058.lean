-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_058
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:07:14.245491+00:00
-- url     : https://prove2.me/submissions/9eed9edc-50ae-46d2-a6fb-a76f8c2f9d5d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_058
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 31, witnessCheck (witnessD7_058 j) = true ∧ (witnessD7_058 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
