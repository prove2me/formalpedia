-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_275
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:15:58.135864+00:00
-- url     : https://prove2.me/submissions/c872bb97-3593-4348-9db4-23f0a988c4b1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_275
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 39, witnessCheck (witnessP9_275 j) = true ∧ (witnessP9_275 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
