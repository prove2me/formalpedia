-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_057
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:40:35.690139+00:00
-- url     : https://prove2.me/submissions/03dd25c7-34fb-4e99-ad1c-dd9a87826cda

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_057
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessP9_057 j) = true ∧ (witnessP9_057 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
