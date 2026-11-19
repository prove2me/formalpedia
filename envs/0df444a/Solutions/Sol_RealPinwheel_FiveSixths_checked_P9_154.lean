-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_154
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:00:16.805775+00:00
-- url     : https://prove2.me/submissions/a8b4cedd-da72-4ed0-a4ec-daacc21d647e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_154
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessP9_154 j) = true ∧ (witnessP9_154 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
