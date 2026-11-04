-- Prove2me | solution 1 for ThreeSum.HierarchyScales.log_mu_add_one_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:51.474252+00:00
-- url     : https://prove2.me/submissions/cca7b1ec-0efa-4679-be09-8db7c648df25

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_BinomialEntropy_logarithmic_error_tendsto_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Scales_mu_log_ratio_tendsto
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_TrimScales_mu_tendsto_atTop
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
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (mu n + 1 : ℝ) / Real.log n) atTop (𝓝 0) := by
  have he := (BinomialEntropy.logarithmic_error_tendsto_zero
    (c := 1) (by norm_num)).comp TrimScales.mu_tendsto_atTop
  have hh := he.mul mu_log_ratio_tendsto
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hmu : (mu n : ℝ) ≠ 0 := by exact_mod_cast (by omega : mu n ≠ 0)
  simp only [Function.comp_def, Nat.cast_one, one_mul]
  field_simp
end ThreeSum.HierarchyScales
