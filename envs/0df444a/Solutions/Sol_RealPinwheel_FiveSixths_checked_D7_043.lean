-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_043
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:50:04.892959+00:00
-- url     : https://prove2.me/submissions/1ac06241-1024-4fae-9e81-1012a202f2a2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_043
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessD7_043 j) = true ∧ (witnessD7_043 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
