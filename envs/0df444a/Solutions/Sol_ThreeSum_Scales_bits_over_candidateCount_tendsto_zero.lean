-- Prove2me | solution 1 for ThreeSum.Scales.bits_over_candidateCount_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:00:48.674816+00:00
-- url     : https://prove2.me/submissions/1dc5438b-16ad-46d9-8686-182a06d4ed09

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Sqrt
import Definitions.Def_Submission_ThreeSum_Scales
import Theorems.Thm_ThreeSum_Scales_inputBits_tendsto_atTop
import Theorems.Thm_ThreeSum_Scales_primeWindow_ge_two
import Theorems.Thm_ThreeSum_Scales_actual_candidate_density
import Theorems.Thm_ThreeSum_Scales_windowExponent_tendsto_atTop
import Theorems.Thm_ThreeSum_Scales_bits_add_one_le_windowExponent_sq
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution :
    Tendsto (fun n : ℕ => (inputBits n + 1 : ℝ) / candidateCount n) atTop (𝓝 0) := by
  have ht := windowExponent_tendsto_atTop.comp inputBits_tendsto_atTop
  have hu := ((tendsto_pow_const_div_const_pow_of_one_lt 3
    (by norm_num : (1 : ℝ) < 2)).comp ht).const_mul (4 * Real.log 2)
  simp only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · exact Filter.Eventually.of_forall (fun n => by positivity)
  · filter_upwards [actual_candidate_density] with n hC
    have hy := primeWindow_ge_two n
    have hyl : 0 < Real.log (primeWindow n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < primeWindow n))
    have hypo : (0 : ℝ) < primeWindow n := by exact_mod_cast (by omega : 0 < primeWindow n)
    have hlower : (0 : ℝ) < (primeWindow n : ℝ) / (4 * Real.log (primeWindow n)) := by positivity
    have hbits : (inputBits n + 1 : ℝ) ≤ (windowExponent (inputBits n) : ℝ) ^ 2 := by
      exact_mod_cast bits_add_one_le_windowExponent_sq (inputBits n)
    have hs : (0 : ℝ) ≤ windowExponent (inputBits n) := Nat.cast_nonneg _
    have hdiv := div_le_div_of_nonneg_left
      (by positivity : (0 : ℝ) ≤ inputBits n + 1) hlower hC
    change (inputBits n + 1 : ℝ) / candidateCount n ≤
      4 * Real.log 2 * ((windowExponent (inputBits n) : ℝ) ^ 3 /
        (2 : ℝ) ^ windowExponent (inputBits n))
    calc
      (inputBits n + 1 : ℝ) / candidateCount n ≤
          (inputBits n + 1 : ℝ) / ((primeWindow n : ℝ) / (4 * Real.log (primeWindow n))) := hdiv
      _ = ((inputBits n + 1 : ℝ) *
          (4 * (windowExponent (inputBits n) : ℝ) * Real.log 2)) /
            (2 : ℝ) ^ windowExponent (inputBits n) := by
        simp only [primeWindow, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
        field_simp
      _ ≤ ((windowExponent (inputBits n) : ℝ) ^ 2 *
          (4 * (windowExponent (inputBits n) : ℝ) * Real.log 2)) /
            (2 : ℝ) ^ windowExponent (inputBits n) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hbits (by positivity)
      _ = _ := by ring
end ThreeSum.Scales
