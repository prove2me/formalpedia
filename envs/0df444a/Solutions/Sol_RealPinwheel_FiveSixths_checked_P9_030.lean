-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_030
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:00:53.64891+00:00
-- url     : https://prove2.me/submissions/4ce9e638-a629-4e57-a8d0-cd66d3271ee2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_030
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 4, witnessCheck (witnessP9_030 j) = true ∧ (witnessP9_030 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
