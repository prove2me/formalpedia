-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_028
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:41:12.959403+00:00
-- url     : https://prove2.me/submissions/4fb0e102-f457-491d-a29b-d11fb445d2e4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_028
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessD7_028 j) = true ∧ (witnessD7_028 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
