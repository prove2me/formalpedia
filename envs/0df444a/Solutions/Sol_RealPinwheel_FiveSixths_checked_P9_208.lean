-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_208
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:35:25.706176+00:00
-- url     : https://prove2.me/submissions/1bbeab7b-5769-4153-b275-e63b5437b3dd

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_208
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessP9_208 j) = true ∧ (witnessP9_208 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
