-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_107
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:46:29.687613+00:00
-- url     : https://prove2.me/submissions/4e625674-3ff2-480d-9679-25e8b606a51a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_107
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessP9_107 j) = true ∧ (witnessP9_107 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
