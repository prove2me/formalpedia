-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_111
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:47:25.725045+00:00
-- url     : https://prove2.me/submissions/1d030047-4e84-4b76-b6a1-89b49751b65d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_111
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessP9_111 j) = true ∧ (witnessP9_111 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
