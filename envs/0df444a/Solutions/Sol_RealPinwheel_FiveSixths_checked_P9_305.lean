-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_305
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:37:08.38645+00:00
-- url     : https://prove2.me/submissions/1b89e7ca-919a-4820-9043-4852fc05a0bc

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_305
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 53, witnessCheck (witnessP9_305 j) = true ∧ (witnessP9_305 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
