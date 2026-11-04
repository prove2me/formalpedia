-- Prove2me | solution 1 for ThreeSum.HierarchyScales.initial_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:55:19.222348+00:00
-- url     : https://prove2.me/submissions/55ce8b7b-c8be-47a1-8718-e8270722df1c

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HierarchyScales_initialCap_bounds
import Theorems.Thm_ThreeSum_HierarchyScales_initialIndex_le_cap
import Theorems.Thm_ThreeSum_HierarchyScales_residual_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_mem_candidates
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
    (actualSwitch n 0 : ℝ) / mu n ≤ initialTheta + 1 / mu n := by
  have hq := initialIndex_le_cap (blockCount (inputBits n)) hmu
  have hc := (initialCap_bounds (mu n)).2
  have hq' : actualSwitch n 0 ≤ initialCap (mu n) := by
    simpa only [actualSwitch, residual_zero] using hq
  have hbound : (25 : ℝ) * actualSwitch n 0 < (mu n : ℝ) + 25 := by exact_mod_cast lt_of_le_of_lt (Nat.mul_le_mul_left 25 hq') hc
  have hmuR : (0 : ℝ) < mu n := by exact_mod_cast (by omega : 0 < mu n)
  rw [div_le_iff₀ hmuR]
  have hid : (initialTheta + 1 / (mu n : ℝ)) * mu n = (mu n : ℝ) / 25 + 1 := by
    unfold initialTheta
    field_simp
  rw [hid]
  linarith
end ThreeSum.HierarchyScales
