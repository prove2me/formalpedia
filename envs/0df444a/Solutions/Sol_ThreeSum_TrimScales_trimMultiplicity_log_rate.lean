-- Prove2me | solution 1 for ThreeSum.TrimScales.trimMultiplicity_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:27:03.514983+00:00
-- url     : https://prove2.me/submissions/a276a4a8-60c0-46b3-821d-f462f244dfcd

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_WeightedCache3SUM_Alias_8c840be79f696836
import Theorems.Thm_ThreeSum_TrimScales_localBucketCap_log_rate
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
    Tendsto (fun n : ℕ => Real.log (trimMultiplicity n : ℝ) / Real.log n) atTop
      (𝓝 (Parameters.kappa / 5)) := by
  have h := (replicatedHalf_log_rate localBucketCap_log_rate).const_mul 2
  have heq : 2 * (Parameters.kappa / 2 / 5) = Parameters.kappa / 5 := by ring
  rw [heq] at h
  convert h using 1
  funext n
  simp only [trimMultiplicity, replicatedHalf, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
  ring
end ThreeSum.TrimScales
