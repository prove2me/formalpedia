-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_144
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:09:54.941283+00:00
-- url     : https://prove2.me/submissions/36ae0249-940b-4d16-a809-b58287a9be79

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_144
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessD8_144 j) = true ∧ (witnessD8_144 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
