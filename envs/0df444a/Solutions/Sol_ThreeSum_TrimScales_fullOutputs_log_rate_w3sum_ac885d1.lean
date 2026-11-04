-- Prove2me | solution 1 for ThreeSum.TrimScales.fullOutputs_log_rate_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:21:52.805287+00:00
-- url     : https://prove2.me/submissions/c18009fd-707a-47d6-b6e7-ed80800e657a

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Theorems.Thm_ThreeSum_TrimScales_mu_tendsto_atTop
import Theorems.Thm_ThreeSum_BinomialEntropy_output_table_rate
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Scales_mu_log_ratio_tendsto
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.TrimScales
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (fullOutputs n : ℝ) / Real.log n) atTop
      (𝓝 (2 * Parameters.E / 5)) := by
  have hm := BinomialEntropy.output_table_rate.comp mu_tendsto_atTop
  have hs := mu_log_ratio_tendsto.const_mul (Real.log 2)
  have h := hm.mul hs
  have heq : 2 * Parameters.E * (Real.log 2 * (1 / (5 * Real.log 2))) =
      2 * Parameters.E / 5 := by field_simp
  rw [heq] at h
  apply h.congr'
  filter_upwards [mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (mu n : ℝ) ≠ 0 := by exact_mod_cast (by omega : mu n ≠ 0)
  simp only [Function.comp_def, fullOutputs]
  field_simp
end ThreeSum.TrimScales
