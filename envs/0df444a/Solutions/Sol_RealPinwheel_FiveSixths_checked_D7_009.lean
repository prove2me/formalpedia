-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_009
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:20:48.410858+00:00
-- url     : https://prove2.me/submissions/500bb9c0-ad95-40f2-adc6-81bf9849387f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_009
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD7_009 j) = true ∧ (witnessD7_009 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
