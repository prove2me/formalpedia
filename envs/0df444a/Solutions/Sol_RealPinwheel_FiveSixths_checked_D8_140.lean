-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_140
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:04:49.730787+00:00
-- url     : https://prove2.me/submissions/828f5b58-89fe-4ab8-82c5-019db128d349

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_140
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessD8_140 j) = true ∧ (witnessD8_140 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
