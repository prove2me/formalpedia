-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_211
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:58:37.873213+00:00
-- url     : https://prove2.me/submissions/5ba986d7-4474-43b4-8a62-df5c9fbcdc80

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_211
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessD8_211 j) = true ∧ (witnessD8_211 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
