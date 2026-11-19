-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_233
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:19:24.55157+00:00
-- url     : https://prove2.me/submissions/6b0a274f-ffd0-494b-aa4d-e13442422dae

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_233
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 31, witnessCheck (witnessD8_233 j) = true ∧ (witnessD8_233 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
