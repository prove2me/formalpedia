-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_037
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:05:20.016635+00:00
-- url     : https://prove2.me/submissions/348906b0-18ae-4fa5-8644-dd772283eee9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_037
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_037 j) = true ∧ (witnessP9_037 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
