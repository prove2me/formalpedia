-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_140
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:34:49.421922+00:00
-- url     : https://prove2.me/submissions/b4af3bc1-eab5-42de-955f-68b9b6cd57b5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_140
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessP9_140 j) = true ∧ (witnessP9_140 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
