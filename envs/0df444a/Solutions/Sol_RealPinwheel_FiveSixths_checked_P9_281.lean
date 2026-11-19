-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_281
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:24:15.51517+00:00
-- url     : https://prove2.me/submissions/8bbf987d-e379-4d1b-b730-170f505276e9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_281
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 41, witnessCheck (witnessP9_281 j) = true ∧ (witnessP9_281 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
