-- Prove2me | solution 1 for ThreeSum.BudgetTime.compiledBudget_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:16:01.909254+00:00
-- url     : https://prove2.me/submissions/6a26d882-a65b-45fb-aead-c1db57ba7479

import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_851b6603dbe122fe
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mono_exponent
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_UniformStageBounds_workBudget_powerBound
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
    PowerBound (compiledBudget a b C k) certificateExponent := by
  have hmain := (PowerBound.const a).mul (workBudget_powerBound C k)
  have hmain' : PowerBound (fun n => a * workBudget C k n) certificateExponent := by
    simpa only [zero_add] using hmain
  have hconst : PowerBound (fun _ : ℕ => b) certificateExponent :=
    (PowerBound.const b).mono_exponent (by norm_num [certificateExponent])
  exact hmain'.add_same hconst
end ThreeSum.BudgetTime
