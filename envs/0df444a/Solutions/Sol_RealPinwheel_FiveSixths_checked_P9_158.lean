-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_158
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:58:52.565426+00:00
-- url     : https://prove2.me/submissions/33ead5dc-77bb-4768-9870-7562ad80c4f0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_158
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessP9_158 j) = true ∧ (witnessP9_158 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
