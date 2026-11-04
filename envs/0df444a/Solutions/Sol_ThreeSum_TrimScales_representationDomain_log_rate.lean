-- Prove2me | solution 1 for ThreeSum.TrimScales.representationDomain_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:12:19.879769+00:00
-- url     : https://prove2.me/submissions/b70ed9ea-b05b-4b60-8dec-d5114d98b1ee

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
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
    Tendsto (fun n : ℕ => Real.log (representationDomain n : ℝ) / Real.log n) atTop
      (𝓝 (1 / 5)) := by
  have h := mu_log_ratio_tendsto.const_mul (Real.log 2)
  have heq : Real.log 2 * (1 / (5 * Real.log 2)) = (1 / 5 : ℝ) := by field_simp
  rw [heq] at h
  convert h using 1
  funext n
  simp only [representationDomain, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  ring
end ThreeSum.TrimScales
