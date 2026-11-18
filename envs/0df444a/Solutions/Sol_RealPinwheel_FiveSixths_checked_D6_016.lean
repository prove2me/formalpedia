-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_016
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:31:38.336993+00:00
-- url     : https://prove2.me/submissions/6fe24c75-fbf1-4215-85d7-bd308ffc1d43

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_016
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 65, witnessCheck (witnessD6_016 j) = true ∧ (witnessD6_016 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
