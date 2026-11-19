-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_263
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:11:27.155505+00:00
-- url     : https://prove2.me/submissions/73d9a490-a4a9-4de1-a431-54c27fbfd28e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_263
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 35, witnessCheck (witnessP9_263 j) = true ∧ (witnessP9_263 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
