-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_025
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:43:48.428764+00:00
-- url     : https://prove2.me/submissions/4c1d7136-ed14-4133-9ba5-f9f076ee0acb

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_025
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessD8_025 j) = true ∧ (witnessD8_025 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
