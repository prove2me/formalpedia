-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_131
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:14:54.379644+00:00
-- url     : https://prove2.me/submissions/e5608328-3190-472c-bf01-d36b3ca25e03

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_131
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessP9_131 j) = true ∧ (witnessP9_131 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
