-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_307
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:38:27.55499+00:00
-- url     : https://prove2.me/submissions/aaf63b3f-d96c-466c-82d0-7c70452666db

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_307
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 55, witnessCheck (witnessP9_307 j) = true ∧ (witnessP9_307 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
