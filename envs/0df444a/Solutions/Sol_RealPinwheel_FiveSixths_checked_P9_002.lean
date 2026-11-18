-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_002
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:39:54.94647+00:00
-- url     : https://prove2.me/submissions/b4887b66-3fa6-48a8-9a62-93e5b81f00ce

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_002
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 1, witnessCheck (witnessP9_002 j) = true ∧ (witnessP9_002 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
