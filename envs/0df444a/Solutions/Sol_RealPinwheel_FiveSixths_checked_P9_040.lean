-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_040
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:11:34.448246+00:00
-- url     : https://prove2.me/submissions/4e395c74-0ee0-4314-9142-5140055a4d36

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_040
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_040 j) = true ∧ (witnessP9_040 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
