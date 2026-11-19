-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_008
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:52:40.519111+00:00
-- url     : https://prove2.me/submissions/b5e9427e-359a-4a4f-a331-fb8dbd49cdd1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_008
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 1, witnessCheck (witnessP9_008 j) = true ∧ (witnessP9_008 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
