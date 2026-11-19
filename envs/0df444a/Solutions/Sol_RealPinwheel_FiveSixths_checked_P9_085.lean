-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_085
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:17:53.963102+00:00
-- url     : https://prove2.me/submissions/902d729e-beec-4c8a-8ba0-f4a002ba6c1e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_085
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessP9_085 j) = true ∧ (witnessP9_085 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
