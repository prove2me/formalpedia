-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_056
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:39:53.443926+00:00
-- url     : https://prove2.me/submissions/cdebd269-a167-4031-b54c-8929337ed08b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_056
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessP9_056 j) = true ∧ (witnessP9_056 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
