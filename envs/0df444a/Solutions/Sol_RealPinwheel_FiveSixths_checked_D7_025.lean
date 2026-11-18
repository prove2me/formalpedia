-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_025
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:38:37.179279+00:00
-- url     : https://prove2.me/submissions/2b5ad676-447b-4ddc-b318-efa1bb548e00

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_025
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessD7_025 j) = true ∧ (witnessD7_025 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
