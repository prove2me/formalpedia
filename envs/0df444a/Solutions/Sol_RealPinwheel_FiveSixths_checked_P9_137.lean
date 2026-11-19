-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_137
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:32:31.848873+00:00
-- url     : https://prove2.me/submissions/c127d320-1d28-4299-9313-bef02225cef5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_137
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessP9_137 j) = true ∧ (witnessP9_137 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
