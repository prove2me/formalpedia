-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_039
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:48:14.752409+00:00
-- url     : https://prove2.me/submissions/9f8da409-eb5a-4bc4-8453-23afa5b39800

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_039
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessD7_039 j) = true ∧ (witnessD7_039 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
