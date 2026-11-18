-- Prove2me | solution 1 for RealPinwheel.FiveSixths.task_checked_P9_000_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:05:36.676202+00:00
-- url     : https://prove2.me/submissions/9a4560db-f675-4f3a-814b-7b75a8b1f3a9

import Definitions.Def_RealPinwheel_FiveSixths_TaskWitnessCheck
import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_000
open RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution (j : Fin 1) (i : Fin 3) : taskWitnessCheck (witnessP9_000 j) (⟨6 + i.val, by omega⟩ : Fin 9) = true := by
  fin_cases j <;> fin_cases i <;> decide +kernel
