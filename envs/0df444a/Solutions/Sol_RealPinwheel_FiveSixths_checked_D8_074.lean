-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_074
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:08:28.865907+00:00
-- url     : https://prove2.me/submissions/86295897-3598-4106-8dfa-421eb701bcc0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_074
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessD8_074 j) = true ∧ (witnessD8_074 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
