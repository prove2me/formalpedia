-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_099
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:31:04.8762+00:00
-- url     : https://prove2.me/submissions/4cf5d7bf-c613-48a5-8f84-eba35066cdca

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_099
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessP9_099 j) = true ∧ (witnessP9_099 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
