-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_010
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:42:22.383725+00:00
-- url     : https://prove2.me/submissions/edf96eeb-f4ba-4a42-b79c-7765cfb91b16

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_010
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 2, witnessCheck (witnessP9_010 j) = true ∧ (witnessP9_010 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
