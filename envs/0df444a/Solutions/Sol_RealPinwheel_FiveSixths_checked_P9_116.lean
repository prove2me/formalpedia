-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_116
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:53:13.960447+00:00
-- url     : https://prove2.me/submissions/7510427e-82c1-4a82-bd3b-f0f654efa74d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_116
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessP9_116 j) = true ∧ (witnessP9_116 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
