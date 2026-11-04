-- Prove2me | solution 1 for ThreeSum.TrimScales.replicatedHalf_log_rate_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:12:18.730892+00:00
-- url     : https://prove2.me/submissions/b08bfd65-1a94-47c4-b78a-5975b6b41c09

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Scales_inputBits_tendsto_atTop
import Theorems.Thm_ThreeSum_Scales_microHalf_tendsto_atTop
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
theorem _root_.solution {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun h : ℕ => Real.log (f h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => Real.log (replicatedHalf f n : ℝ) / Real.log n) atTop (𝓝 (a / 5)) := by
  have hl := hf.comp (microHalf_tendsto_atTop.comp inputBits_tendsto_atTop)
  have hs := mu_log_ratio_tendsto.const_mul (Real.log 2)
  have h := hl.mul hs
  have hlim : a * (Real.log 2 * (1 / (5 * Real.log 2))) = a / 5 := by field_simp
  rw [hlim] at h
  apply h.congr'
  filter_upwards [(microHalf_tendsto_atTop.comp inputBits_tendsto_atTop).eventually
      (eventually_ge_atTop 1)] with n hn
  change 1 ≤ microHalf (inputBits n) at hn
  have hn0 : (microHalf (inputBits n) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : microHalf (inputBits n) ≠ 0)
  simp only [Function.comp_def, replicatedHalf, Nat.cast_pow, Real.log_pow]
  have hmu : (mu n : ℝ) = (blockCount (inputBits n) : ℝ) *
      (2 * microHalf (inputBits n)) := by simp [mu, totalSize, microSize, microHalf]
  rw [hmu]
  field_simp
end ThreeSum.TrimScales
