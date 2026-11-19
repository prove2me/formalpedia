-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_194
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:19:57.106937+00:00
-- url     : https://prove2.me/submissions/9557ed43-7770-48fb-b91b-e87048fece87

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_194
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessP9_194 j) = true ∧ (witnessP9_194 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
