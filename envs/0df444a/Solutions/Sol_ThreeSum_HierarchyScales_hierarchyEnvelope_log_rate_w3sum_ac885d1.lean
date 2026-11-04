-- Prove2me | solution 1 for ThreeSum.HierarchyScales.hierarchyEnvelope_log_rate_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:26:33.589838+00:00
-- url     : https://prove2.me/submissions/7296a7e7-64a4-4edc-8947-28e829c4fe4c

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HierarchyScales_log_mu_add_one_rate
import Theorems.Thm_ThreeSum_Asymptotics_log_nat_tendsto_atTop
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Scales_mu_log_ratio_tendsto
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
theorem _root_.solution (C B : ℝ) :
    Tendsto (fun n : ℕ => Real.log (hierarchyEnvelope C B n) / Real.log n) atTop (𝓝 (C / 5)) := by
  have hm := mu_log_ratio_tendsto.const_mul (Real.log 2 * C)
  have hid : Real.log 2 * C * (1 / (5 * Real.log 2)) = C / 5 := by field_simp
  rw [hid] at hm
  have hc := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul B
  have hh := log_mu_add_one_rate.add (hm.add hc)
  simp only [mul_zero, add_zero, zero_add] at hh
  convert hh using 1
  funext n
  have hp : (mu n + 1 : ℝ) ≠ 0 := by positivity
  simp only [hierarchyEnvelope, Real.log_mul hp (Real.exp_ne_zero _), Real.log_exp,
    Pi.inv_apply, add_div]
  ring
end ThreeSum.HierarchyScales
