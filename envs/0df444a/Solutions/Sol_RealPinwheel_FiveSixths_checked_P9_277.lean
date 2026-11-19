-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_277
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:16:49.527325+00:00
-- url     : https://prove2.me/submissions/7a4c814d-890b-4cfe-b82c-e79e94a679a2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_277
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 41, witnessCheck (witnessP9_277 j) = true ∧ (witnessP9_277 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
