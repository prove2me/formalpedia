-- Prove2me | solution 1 for ThreeSum.HierarchyScales.initial_query_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:29:21.793067+00:00
-- url     : https://prove2.me/submissions/63c50879-b778-46d3-a496-50c97dcc0968

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HierarchyScales_residual_zero
import Theorems.Thm_ThreeSum_HierarchyScales_initial_ratio_le
import Theorems.Thm_ThreeSum_HierarchyScales_initial_upper_mem
import Theorems.Thm_ThreeSum_BinomialEntropy_log_choose_entropy_bounds
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_actual_depth_condition
import Theorems.Thm_ThreeSum_Switch_actual_residual_even
import Theorems.Thm_ThreeSum_Switch_actual_residual_pos
import Definitions.Def_WeightedCache3SUM_Alias_99dfc3473a1cfe41
import Theorems.Thm_ThreeSum_Switch_actual_totalSize
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_Switch_switchIndex_spec
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.HierarchyScales
theorem _root_.solution {n : ℕ} (hmu : 50 ≤ mu n) :
    Real.log (queryTerms n 0 : ℝ) ≤
      (mu n : ℝ) * Real.log 2 * entropy (initialTheta + 1 / (mu n : ℝ)) := by
  have hm : 0 < mu n := by omega
  have ht := (actual_switch_certified (j := 0) hm (by omega)).1
  rw [residual_zero] at ht
  have hupper := initial_upper_mem hmu
  have hmono := Real.binEntropy_strictMonoOn.monotoneOn
    (by simpa only [one_div] using ht)
    (by simpa only [one_div] using hupper) (initial_ratio_le hmu)
  have hprod := hm
  rw [actual_totalSize] at hprod
  have hq := (switchIndex_spec (Nat.pos_of_mul_pos_right hprod)
    (actual_depth_condition (n := n) (j := 0) (by omega))
    (actual_residual_pos hm (by omega)) (actual_residual_even n 0)).1
  have hb := (BinomialEntropy.log_choose_entropy_bounds
    (hq.trans (Nat.div_le_self _ _))).2
  change Real.log (queryTerms n 0 : ℝ) ≤
    (residualSize n 0 : ℝ) * Real.binEntropy ((actualSwitch n 0 : ℝ) / residualSize n 0) at hb
  rw [residual_zero] at hb
  have hmul := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg (α := ℝ) (mu n))
  have hid : (mu n : ℝ) * Real.log 2 * entropy (initialTheta + 1 / (mu n : ℝ)) =
      (mu n : ℝ) * Real.binEntropy (initialTheta + 1 / (mu n : ℝ)) := by
    unfold entropy
    field_simp
  rw [hid]
  exact hb.trans hmul
end ThreeSum.HierarchyScales
