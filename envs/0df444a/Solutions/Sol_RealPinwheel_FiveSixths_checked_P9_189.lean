-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_189
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:16:58.437334+00:00
-- url     : https://prove2.me/submissions/721fcd7c-7291-48b6-b886-8666a11e1695

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_189
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 21, witnessCheck (witnessP9_189 j) = true ∧ (witnessP9_189 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
