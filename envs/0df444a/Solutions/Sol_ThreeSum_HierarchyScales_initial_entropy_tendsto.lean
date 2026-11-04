-- Prove2me | solution 1 for ThreeSum.HierarchyScales.initial_entropy_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:19:40.226379+00:00
-- url     : https://prove2.me/submissions/9ebe1377-96bb-45e7-918d-939f6748fe4d

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_mem_candidates
import Theorems.Thm_ThreeSum_TrimScales_mu_cast_tendsto_atTop
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
    Tendsto (fun n : ℕ => entropy (initialTheta + 1 / (mu n : ℝ))) atTop
      (𝓝 (entropy initialTheta)) := by
  have hu := TrimScales.mu_cast_tendsto_atTop.inv_tendsto_atTop.const_add initialTheta
  simp only [add_zero] at hu
  have hc : Continuous entropy := Real.binEntropy_continuous.div_const _
  simpa only [Function.comp_def, one_div, Pi.inv_apply] using hc.continuousAt.tendsto.comp hu
end ThreeSum.HierarchyScales
