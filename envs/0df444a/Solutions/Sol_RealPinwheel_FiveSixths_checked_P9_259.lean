-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_259
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:07:24.209337+00:00
-- url     : https://prove2.me/submissions/68a86e48-f8ca-400b-b612-1724df5a4a19

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_259
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 35, witnessCheck (witnessP9_259 j) = true ∧ (witnessP9_259 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
