-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget.fold_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:35:40.382904+00:00
-- url     : https://prove2.me/submissions/bee6f5b0-7bf3-4075-9f6a-9aca857c86e0

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentReporter
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentReporterBudget

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget
open Light TernaryMomentSchedule TernaryWeightChannels
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget
theorem _root_.solution (xs : List (ℕ×ℕ)) :
    1000≤xs.foldr (fun c n => max (circuitCost c) n) 1000 := by
  induction xs with
  | nil => rfl
  | cons c cs ih => exact ih.trans (Nat.le_max_right _ _)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentReporterBudget
