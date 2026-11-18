-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_048
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:56:11.781172+00:00
-- url     : https://prove2.me/submissions/3ddfad2d-8a19-450f-b5a7-7d018036e54d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_048
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 26, witnessCheck (witnessD7_048 j) = true ∧ (witnessD7_048 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
