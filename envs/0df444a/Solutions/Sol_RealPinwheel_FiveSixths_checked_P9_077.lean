-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_077
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:04:31.73104+00:00
-- url     : https://prove2.me/submissions/eca28226-4846-44db-b90d-b23bca4d644c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_077
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessP9_077 j) = true ∧ (witnessP9_077 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
