-- Prove2me | solution 1 for ThreeSum.BandScales.bandDivisor_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:12:21.105589+00:00
-- url     : https://prove2.me/submissions/03626a56-ebb2-47d8-800c-c57751dd1761

import Definitions.Def_Submission_ThreeSum_TrimScales
import Definitions.Def_Submission_ThreeSum_BandScales
import Theorems.Thm_ThreeSum_BandScales_mu_div_twenty_real
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Scales_mu_log_ratio_tendsto
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.BandScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section
namespace ThreeSum.BandScales
theorem _root_.solution :
    Tendsto (fun n : ℕ => Real.log (bandDivisor n : ℝ) / Real.log n) atTop (𝓝 (1 / 100)) := by
  have h := mu_log_ratio_tendsto.const_mul (Real.log 2 / 20)
  have heq : (Real.log 2 / 20) * (1 / (5 * Real.log 2)) = (1 / 100 : ℝ) := by field_simp; norm_num
  rw [heq] at h
  convert h using 1
  funext n
  simp only [bandDivisor, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, mu_div_twenty_real]
  ring
end ThreeSum.BandScales
