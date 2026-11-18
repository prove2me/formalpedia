-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_057
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:07:00.459206+00:00
-- url     : https://prove2.me/submissions/bc251ff0-96c7-498b-b9d5-2c9a3cee4942

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_057
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 31, witnessCheck (witnessD7_057 j) = true ∧ (witnessD7_057 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
