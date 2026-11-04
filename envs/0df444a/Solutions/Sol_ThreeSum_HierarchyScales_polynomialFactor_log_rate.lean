-- Prove2me | solution 1 for ThreeSum.HierarchyScales.polynomialFactor_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:41.298019+00:00
-- url     : https://prove2.me/submissions/589994d7-4c65-48da-8390-0226b0452e7e

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HierarchyScales_log_mu_add_one_rate
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
theorem _root_.solution (C : ℕ) :
    Tendsto (fun n : ℕ => Real.log (polynomialFactor C n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have hh := log_mu_add_one_rate.const_mul (C : ℝ)
  simp only [mul_zero] at hh
  simpa only [polynomialFactor, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.log_pow,
    mul_div_assoc] using hh
end ThreeSum.HierarchyScales
