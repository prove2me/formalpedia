-- Prove2me | solution 1 for ThreeSum.TrimScales.localLength_log_rate_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:14.554024+00:00
-- url     : https://prove2.me/submissions/9b050667-a9d4-4467-a7dc-90fe2d913cfa

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
import Theorems.Thm_ThreeSum_TrimScales_localLength_pos
import Theorems.Thm_ThreeSum_TrimScales_localLength_quadratic_bound
import Theorems.Thm_ThreeSum_BinomialEntropy_logarithmic_error_tendsto_zero
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
    Tendsto (fun h : ℕ => Real.log (localLength h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
  have hlog := BinomialEntropy.logarithmic_error_tendsto_zero (c := 1) (by norm_num)
  have hinv := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hu := (hinv.const_mul (19 / 2 : ℝ)).add (hlog.div_const (Real.log 2))
  simp only [mul_zero, zero_div, zero_add] at hu
  apply squeeze_zero' _ _ hu
  · exact Filter.Eventually.of_forall (fun h =>
      div_nonneg (Real.log_natCast_nonneg _) (by positivity))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
    have hhpos : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
    have hlen : (0 : ℝ) < localLength h := by exact_mod_cast localLength_pos h
    have hb : (localLength h : ℝ) ≤ (2 : ℝ) ^ 19 * (h + 1) ^ 2 := by
      exact_mod_cast localLength_quadratic_bound h
    have hlogb := Real.log_le_log hlen hb
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlogb
    have hd := div_le_div_of_nonneg_right hlogb (by positivity :
      (0 : ℝ) ≤ (2 * h : ℝ) * Real.log 2)
    apply le_of_le_of_eq hd
    simp only [one_mul, Pi.inv_apply, Nat.cast_ofNat]
    field_simp
    ring
end ThreeSum.TrimScales
