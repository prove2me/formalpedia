-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_190
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:10:30.901725+00:00
-- url     : https://prove2.me/submissions/be01ae79-9636-4f61-9879-1d463cad54f4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_190
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 21, witnessCheck (witnessP9_190 j) = true ∧ (witnessP9_190 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
