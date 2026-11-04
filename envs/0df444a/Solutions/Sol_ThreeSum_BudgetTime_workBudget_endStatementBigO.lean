-- Prove2me | solution 1 for ThreeSum.BudgetTime.workBudget_endStatementBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:18:10.170692+00:00
-- url     : https://prove2.me/submissions/8c988931-2bac-457b-9f42-775b0edd9008

import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Theorems.Thm_ThreeSum_BudgetTime_endStatementBigO_of_eventually_le_rpow
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_UniformStageBounds_workBudget_eventually_target
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
theorem _root_.solution (C k : ℕ) :
    EndStatement.BigO (workBudget C k) (981 / 500) := by
  apply endStatementBigO_of_eventually_le_rpow (by norm_num)
  simpa [targetExponent] using workBudget_eventually_target C k
end ThreeSum.BudgetTime
