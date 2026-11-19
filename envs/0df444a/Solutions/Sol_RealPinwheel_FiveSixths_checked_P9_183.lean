-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_183
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:07:07.098212+00:00
-- url     : https://prove2.me/submissions/1f052cbc-5569-45af-a6b0-9f32ae3618b4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_183
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 20, witnessCheck (witnessP9_183 j) = true ∧ (witnessP9_183 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
