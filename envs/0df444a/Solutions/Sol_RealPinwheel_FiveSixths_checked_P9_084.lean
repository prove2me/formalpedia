-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_084
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:08:31.50025+00:00
-- url     : https://prove2.me/submissions/dc15a821-d7c3-42db-b10a-1eb814ffdd55

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_084
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessP9_084 j) = true ∧ (witnessP9_084 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
