-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_053
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:58:58.92583+00:00
-- url     : https://prove2.me/submissions/c406ef16-026e-4314-868d-73fc24b8bf71

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_053
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessD8_053 j) = true ∧ (witnessD8_053 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
