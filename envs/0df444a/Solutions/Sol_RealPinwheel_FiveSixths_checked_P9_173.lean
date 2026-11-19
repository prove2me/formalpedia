-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_173
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:01:07.165581+00:00
-- url     : https://prove2.me/submissions/06bfb2be-20ef-42b1-9982-2985f01e16c9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_173
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 18, witnessCheck (witnessP9_173 j) = true ∧ (witnessP9_173 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
