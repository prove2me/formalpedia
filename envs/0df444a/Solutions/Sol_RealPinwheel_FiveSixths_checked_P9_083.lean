-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_083
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:10:22.663314+00:00
-- url     : https://prove2.me/submissions/66831b3b-1e9d-4589-986a-32d8441b32d2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_083
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessP9_083 j) = true ∧ (witnessP9_083 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
