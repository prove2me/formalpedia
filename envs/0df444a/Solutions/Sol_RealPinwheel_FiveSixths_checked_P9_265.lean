-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_265
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:12:51.131874+00:00
-- url     : https://prove2.me/submissions/2eb58fec-c094-4dad-b6cd-151f083cb649

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_265
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 37, witnessCheck (witnessP9_265 j) = true ∧ (witnessP9_265 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
