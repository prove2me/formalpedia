-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_245
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:33:43.795084+00:00
-- url     : https://prove2.me/submissions/85689dd8-4692-4200-a93f-567892187267

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_245
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 48, witnessCheck (witnessD8_245 j) = true ∧ (witnessD8_245 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
