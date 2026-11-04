-- Prove2me | solution 1 for ThreeSum.BudgetTime.compiledBudget_eventually_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:18:29.334887+00:00
-- url     : https://prove2.me/submissions/f15e8ba7-d6eb-4a4a-99d9-d2ce7db737e8

import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Theorems.Thm_ThreeSum_BudgetTime_compiledBudget_powerBound
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Parameters_certificate_lt_target
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.BudgetTime
open Filter Real ThreeSum.Parameters ThreeSum.StageBounds
  ThreeSum.UniformStageBounds
open scoped Topology
set_option maxHeartbeats 400000
namespace ThreeSum.BudgetTime
theorem _root_.solution (a b C k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (compiledBudget a b C k n : ℝ) ≤ (n : ℝ) ^ targetExponent := by
  have h := compiledBudget_powerBound a b C k
    (targetExponent - certificateExponent) (sub_pos.mpr certificate_lt_target)
  have heq : certificateExponent + (targetExponent - certificateExponent) = targetExponent := by ring
  simpa only [heq] using h
end ThreeSum.BudgetTime
