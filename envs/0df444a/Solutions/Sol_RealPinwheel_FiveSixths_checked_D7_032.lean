-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_032
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:43:07.662033+00:00
-- url     : https://prove2.me/submissions/84b9a051-3384-4b7e-b166-584b6e55763e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_032
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessD7_032 j) = true ∧ (witnessD7_032 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
