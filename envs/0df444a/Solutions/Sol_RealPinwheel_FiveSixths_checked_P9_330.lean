-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_330
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:50:29.139163+00:00
-- url     : https://prove2.me/submissions/3a647fee-862c-4a80-9982-eefc343d8b51

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_330
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 89, witnessCheck (witnessP9_330 j) = true ∧ (witnessP9_330 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
