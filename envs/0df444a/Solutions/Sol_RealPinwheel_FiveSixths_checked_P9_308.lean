-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_308
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:38:35.147442+00:00
-- url     : https://prove2.me/submissions/0c9b138d-0417-4d5f-9963-155a3d46cbfa

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_308
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 55, witnessCheck (witnessP9_308 j) = true ∧ (witnessP9_308 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
