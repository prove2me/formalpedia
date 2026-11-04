-- Prove2me | solution 1 for ThreeSum.WeightedGlobalMomentReporterBudget.fold_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:33:23.991797+00:00
-- url     : https://prove2.me/submissions/ee738024-1aae-4b38-bd36-722c55dad8a0

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentReporter
import Definitions.Def_Submission_Weighted_Global_TernaryMomentReporterBudget

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalMomentReporterBudget
open Light TernaryMomentSchedule TernaryWeightChannels
namespace ThreeSum.WeightedGlobalMomentReporterBudget
theorem _root_.solution (xs : List (ℕ×ℕ)) :
    1000≤xs.foldr (fun c n => max (circuitCost c) n) 1000 := by
  induction xs with
  | nil => rfl
  | cons c cs ih => exact ih.trans (Nat.le_max_right _ _)
end ThreeSum.WeightedGlobalMomentReporterBudget
