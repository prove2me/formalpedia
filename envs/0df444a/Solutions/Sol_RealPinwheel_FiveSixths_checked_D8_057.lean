-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_057
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:58:35.441198+00:00
-- url     : https://prove2.me/submissions/a4673e25-702a-4ea1-9605-85167f649347

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_057
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessD8_057 j) = true ∧ (witnessD8_057 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
