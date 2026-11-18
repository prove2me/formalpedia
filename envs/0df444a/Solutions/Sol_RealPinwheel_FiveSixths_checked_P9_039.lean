-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_039
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:11:33.875937+00:00
-- url     : https://prove2.me/submissions/59a24a8f-ec70-4a14-9403-1e0716eadf16

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_039
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_039 j) = true ∧ (witnessP9_039 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
