-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_106
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:44:33.879735+00:00
-- url     : https://prove2.me/submissions/10cc0177-7001-437a-b48b-f17d3be73373

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_106
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessP9_106 j) = true ∧ (witnessP9_106 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
