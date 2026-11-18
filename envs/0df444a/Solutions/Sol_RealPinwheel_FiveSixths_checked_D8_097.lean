-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_097
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:24:53.691491+00:00
-- url     : https://prove2.me/submissions/1c9c2db3-5c70-44b6-aaf9-06f9a8c3d50f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_097
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessD8_097 j) = true ∧ (witnessD8_097 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
