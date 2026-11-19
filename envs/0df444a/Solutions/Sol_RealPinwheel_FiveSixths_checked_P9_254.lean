-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_254
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:05:49.452922+00:00
-- url     : https://prove2.me/submissions/f6710d9c-fb11-4382-b8e1-f1911e3d5ebb

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_254
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 34, witnessCheck (witnessP9_254 j) = true ∧ (witnessP9_254 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
