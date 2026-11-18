-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_000
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:13:22.760584+00:00
-- url     : https://prove2.me/submissions/21bd56db-9bc8-4364-bc08-3778166341d8

import Theorems.Thm_RealPinwheel_FiveSixths_task_checked_P9_000_0
import Theorems.Thm_RealPinwheel_FiveSixths_task_checked_P9_000_1
import Theorems.Thm_RealPinwheel_FiveSixths_task_checked_P9_000_2
open RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ j : Fin 1, witnessCheck (witnessP9_000 j) = true ∧ (witnessP9_000 j).length ≤ 1800  := by
  intro j
  constructor
  · change (decide (0 < (witnessP9_000 j).length) && (List.finRange 9).all (taskWitnessCheck (witnessP9_000 j))) = true
    rw [Bool.and_eq_true]
    constructor
    · fin_cases j <;> decide +kernel
    · apply List.all_eq_true.mpr
      intro i hi
      fin_cases i
      · exact RealPinwheel.FiveSixths.task_checked_P9_000_0 j ⟨0, by decide⟩
      · exact RealPinwheel.FiveSixths.task_checked_P9_000_0 j ⟨1, by decide⟩
      · exact RealPinwheel.FiveSixths.task_checked_P9_000_0 j ⟨2, by decide⟩
      · exact RealPinwheel.FiveSixths.task_checked_P9_000_1 j ⟨0, by decide⟩
      · exact RealPinwheel.FiveSixths.task_checked_P9_000_1 j ⟨1, by decide⟩
      · exact RealPinwheel.FiveSixths.task_checked_P9_000_1 j ⟨2, by decide⟩
      · exact RealPinwheel.FiveSixths.task_checked_P9_000_2 j ⟨0, by decide⟩
      · exact RealPinwheel.FiveSixths.task_checked_P9_000_2 j ⟨1, by decide⟩
      · exact RealPinwheel.FiveSixths.task_checked_P9_000_2 j ⟨2, by decide⟩
  · fin_cases j <;> decide +kernel
