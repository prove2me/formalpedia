-- Prove2me | solution 1 for ThreeSum.TrimScales.representationBound_eventually_le_domain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:41:14.991503+00:00
-- url     : https://prove2.me/submissions/7e9fae1a-c72b-4ba2-963e-0cea00aebd08

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Theorems.Thm_ThreeSum_TrimScales_mu_tendsto_atTop
import Theorems.Thm_ThreeSum_TrimScales_representationBound_log_domain_rate
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
theorem _root_.solution {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (representationBound n : ℝ) ≤
      (representationDomain n : ℝ) ^ (Parameters.kappa + d) := by
  have hs := representationBound_log_domain_rate.eventually
    (gt_mem_nhds (by linarith : Parameters.kappa < Parameters.kappa + d))
  filter_upwards [hs, mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  have hmupos : (0 : ℝ) < mu n := by exact_mod_cast (by omega : 0 < mu n)
  have hDpos : (0 : ℝ) < representationDomain n := by
    simp only [representationDomain, Nat.cast_pow, Nat.cast_ofNat]
    positivity
  have hDlog : 0 < Real.log (representationDomain n : ℝ) := by
    simp only [representationDomain, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    positivity
  exact Real.le_rpow_of_log_le hDpos ((div_lt_iff₀ hDlog).mp hn).le
end ThreeSum.TrimScales
