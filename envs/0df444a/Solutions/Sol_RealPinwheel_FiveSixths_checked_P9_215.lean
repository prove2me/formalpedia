-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_215
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:40:14.308276+00:00
-- url     : https://prove2.me/submissions/eef3b442-c037-4da1-bfe0-5a9e1ae6ede0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_215
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessP9_215 j) = true ∧ (witnessP9_215 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
