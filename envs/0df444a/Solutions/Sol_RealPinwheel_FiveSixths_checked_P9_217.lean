-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_217
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:51:51.925518+00:00
-- url     : https://prove2.me/submissions/4cf81d52-f4f0-4dbc-8b93-1e0a1afb2c27

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_217
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 26, witnessCheck (witnessP9_217 j) = true ∧ (witnessP9_217 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
