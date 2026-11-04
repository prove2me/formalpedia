-- Prove2me | solution 1 for ThreeSum.TrimScales.representationBound_log_domain_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:37:14.043913+00:00
-- url     : https://prove2.me/submissions/ffc3a9fb-22a9-4b8e-b54a-3c4442062588

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_WeightedCache3SUM_Alias_dc2f19a97a662b74
import Theorems.Thm_ThreeSum_TrimScales_mu_tendsto_atTop
import Theorems.Thm_ThreeSum_TrimScales_representationDomain_log_rate
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
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
    Tendsto (fun n : ℕ => Real.log (representationBound n : ℝ) /
      Real.log (representationDomain n : ℝ)) atTop (𝓝 Parameters.kappa) := by
  have h := representationBound_log_rate.div representationDomain_log_rate
    (by norm_num : (1 / 5 : ℝ) ≠ 0)
  have heq : Parameters.kappa / 5 / (1 / 5) = Parameters.kappa := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  have hmupos : (0 : ℝ) < mu n := by exact_mod_cast (by omega : 0 < mu n)
  have hD : Real.log (representationDomain n : ℝ) ≠ 0 := by
    simp only [representationDomain, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    positivity
  simp only [Pi.div_apply]
  field_simp
end ThreeSum.TrimScales
