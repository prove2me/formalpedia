-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_228
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:16:57.67051+00:00
-- url     : https://prove2.me/submissions/fd493987-52d1-4b4c-97b2-ecef33f49f50

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_228
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 29, witnessCheck (witnessD8_228 j) = true ∧ (witnessD8_228 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
