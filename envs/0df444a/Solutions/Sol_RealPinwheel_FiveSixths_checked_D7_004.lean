-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_004
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:16:30.429502+00:00
-- url     : https://prove2.me/submissions/c765e8f2-e97c-455d-81a5-6757a56f07eb

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_004
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessD7_004 j) = true ∧ (witnessD7_004 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
