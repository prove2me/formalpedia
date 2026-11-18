-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_053
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:58:24.440885+00:00
-- url     : https://prove2.me/submissions/b860d30c-74d9-4a76-a18f-566f31c896c3

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_053
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 29, witnessCheck (witnessD7_053 j) = true ∧ (witnessD7_053 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
