-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_279
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:18:28.159453+00:00
-- url     : https://prove2.me/submissions/d9e2e468-944f-46fd-ad7c-f86da7458e9c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_279
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 41, witnessCheck (witnessP9_279 j) = true ∧ (witnessP9_279 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
