-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_045
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:54:47.019205+00:00
-- url     : https://prove2.me/submissions/8a3c5661-2173-478a-a5d4-bc9a1eb58588

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_045
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessD7_045 j) = true ∧ (witnessD7_045 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
