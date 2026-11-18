-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_031
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:00:54.520428+00:00
-- url     : https://prove2.me/submissions/05a08604-5f8e-4822-ae2f-395c45348d89

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_031
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 4, witnessCheck (witnessP9_031 j) = true ∧ (witnessP9_031 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
