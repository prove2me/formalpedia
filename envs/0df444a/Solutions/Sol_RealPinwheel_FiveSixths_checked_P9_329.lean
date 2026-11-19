-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_329
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:50:16.248189+00:00
-- url     : https://prove2.me/submissions/88354aa3-2233-4767-93a0-f174e27fe186

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_329
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 87, witnessCheck (witnessP9_329 j) = true ∧ (witnessP9_329 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
