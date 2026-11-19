-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_215
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:03:49.680065+00:00
-- url     : https://prove2.me/submissions/b9ba96c8-858a-4638-a467-d108f863bf86

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_215
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 26, witnessCheck (witnessD8_215 j) = true ∧ (witnessD8_215 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
