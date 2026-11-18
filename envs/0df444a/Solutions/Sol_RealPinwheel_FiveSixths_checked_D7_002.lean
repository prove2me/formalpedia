-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_002
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:17:33.6246+00:00
-- url     : https://prove2.me/submissions/88bab310-ac9a-48c3-bcea-36bd67bc67dd

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_002
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessD7_002 j) = true ∧ (witnessD7_002 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
