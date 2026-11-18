-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_063
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:19:47.774955+00:00
-- url     : https://prove2.me/submissions/43553c1d-6a23-4c14-be7d-2f9020179177

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_063
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 35, witnessCheck (witnessD7_063 j) = true ∧ (witnessD7_063 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
