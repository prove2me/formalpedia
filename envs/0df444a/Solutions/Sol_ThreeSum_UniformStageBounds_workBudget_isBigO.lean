-- Prove2me | solution 1 for ThreeSum.UniformStageBounds.workBudget_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:18:08.774129+00:00
-- url     : https://prove2.me/submissions/7879cd43-2d26-4354-aa93-2d20dbb722df

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Theorems.Thm_ThreeSum_UniformStageBounds_workBudget_eventually_target
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.UniformStageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.UniformStageBounds
theorem _root_.solution (C k : ℕ) :
    (fun n : ℕ => (workBudget C k n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ targetExponent) := by
  apply _root_.Asymptotics.IsBigO.of_norm_eventuallyLE
  filter_upwards [workBudget_eventually_target C k] with n hn
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (workBudget C k n)),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) n) targetExponent)] using hn
end ThreeSum.UniformStageBounds
