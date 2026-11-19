-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_309
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:38:57.242735+00:00
-- url     : https://prove2.me/submissions/fc136f9e-dc0e-445a-9d35-4137a68a38e7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_309
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 56, witnessCheck (witnessP9_309 j) = true ∧ (witnessP9_309 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
