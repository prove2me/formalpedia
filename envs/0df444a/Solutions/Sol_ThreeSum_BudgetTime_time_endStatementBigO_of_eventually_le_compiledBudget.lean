-- Prove2me | solution 1 for ThreeSum.BudgetTime.time_endStatementBigO_of_eventually_le_compiledBudget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:21:50.322378+00:00
-- url     : https://prove2.me/submissions/185d0a55-4507-4996-9d68-168c78c7c476

import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Theorems.Thm_ThreeSum_BudgetTime_endStatementBigO_of_eventually_le_rpow
import Theorems.Thm_ThreeSum_BudgetTime_compiledBudget_eventually_target
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
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
theorem _root_.solution
    {T : ℕ → ℕ} {a b C k : ℕ}
    (hT : ∀ᶠ n : ℕ in atTop, T n ≤ compiledBudget a b C k n) :
    EndStatement.BigO T (981 / 500) := by
  apply endStatementBigO_of_eventually_le_rpow (by norm_num)
  filter_upwards [hT, compiledBudget_eventually_target a b C k] with n hcost hbound
  have hcast : (T n : ℝ) ≤ compiledBudget a b C k n := by exact_mod_cast hcost
  simpa [targetExponent] using hcast.trans hbound
end ThreeSum.BudgetTime
