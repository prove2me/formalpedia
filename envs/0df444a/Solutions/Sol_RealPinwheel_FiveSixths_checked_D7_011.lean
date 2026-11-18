-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_011
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:22:11.948+00:00
-- url     : https://prove2.me/submissions/7b6fa686-6cf0-4513-a338-193a715438ee

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_011
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessD7_011 j) = true ∧ (witnessD7_011 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
