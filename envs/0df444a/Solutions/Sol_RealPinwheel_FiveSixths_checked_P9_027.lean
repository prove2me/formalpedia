-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_027
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:59:52.151243+00:00
-- url     : https://prove2.me/submissions/dffed6c4-c91e-4318-b66f-0c856c6e6b95

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_027
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 4, witnessCheck (witnessP9_027 j) = true ∧ (witnessP9_027 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
