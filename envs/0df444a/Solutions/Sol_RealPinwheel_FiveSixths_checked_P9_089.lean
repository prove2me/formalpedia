-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_089
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:24:28.45141+00:00
-- url     : https://prove2.me/submissions/d12b8423-0376-4bda-b3f8-109c4aa0222a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_089
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessP9_089 j) = true ∧ (witnessP9_089 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
