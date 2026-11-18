-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_090
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:21:39.33638+00:00
-- url     : https://prove2.me/submissions/a3a41dd4-dc24-4897-a138-8096342c2257

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_090
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD8_090 j) = true ∧ (witnessD8_090 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
