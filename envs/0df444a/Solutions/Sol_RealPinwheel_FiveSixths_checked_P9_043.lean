-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_043
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:18:12.469172+00:00
-- url     : https://prove2.me/submissions/15cd2451-9179-4a3f-ae70-fe19efc390eb

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_043
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_043 j) = true ∧ (witnessP9_043 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
