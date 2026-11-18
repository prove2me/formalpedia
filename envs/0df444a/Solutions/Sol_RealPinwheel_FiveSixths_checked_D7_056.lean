-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_056
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:05:52.881565+00:00
-- url     : https://prove2.me/submissions/0e7b1689-0fae-4175-aa24-ae09771f384f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_056
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 30, witnessCheck (witnessD7_056 j) = true ∧ (witnessD7_056 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
