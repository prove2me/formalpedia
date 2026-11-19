-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_009
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:50:04.805314+00:00
-- url     : https://prove2.me/submissions/44933d19-d0c2-48ab-bc4e-ee0849c1fc3f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_009
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 2, witnessCheck (witnessP9_009 j) = true ∧ (witnessP9_009 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
