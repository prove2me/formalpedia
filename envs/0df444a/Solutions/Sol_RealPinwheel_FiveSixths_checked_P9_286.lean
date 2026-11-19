-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_286
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:25:11.997114+00:00
-- url     : https://prove2.me/submissions/5296a0a5-758f-464e-99f0-19ba7c912f9d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_286
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 44, witnessCheck (witnessP9_286 j) = true ∧ (witnessP9_286 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
