-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_032
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:59:28.849193+00:00
-- url     : https://prove2.me/submissions/bded29f4-012e-4ee3-a466-881ba54e2a17

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_032
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 4, witnessCheck (witnessP9_032 j) = true ∧ (witnessP9_032 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
