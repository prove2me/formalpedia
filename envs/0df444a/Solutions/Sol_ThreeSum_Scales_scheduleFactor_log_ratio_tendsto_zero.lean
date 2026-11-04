-- Prove2me | solution 1 for ThreeSum.Scales.scheduleFactor_log_ratio_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:12:17.564199+00:00
-- url     : https://prove2.me/submissions/368eb240-049f-4bb9-8142-db3636973fb7

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
import Theorems.Thm_ThreeSum_Scales_mu_log_ratio_tendsto
import Theorems.Thm_ThreeSum_Scales_muZero_tendsto_atTop
import Theorems.Thm_ThreeSum_BinomialEntropy_logarithmic_error_tendsto_zero
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
theorem _root_.solution (C : ℕ) :
    Tendsto (fun n : ℕ => Real.log (scheduleFactor C n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have he := (BinomialEntropy.logarithmic_error_tendsto_zero
    (c := 256) (by norm_num)).comp muZero_tendsto_atTop
  have h := (he.mul mu_log_ratio_tendsto).const_mul (C : ℝ)
  simp only [zero_mul, mul_zero] at h
  apply h.congr'
  filter_upwards [muZero_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (muZero n : ℝ) ≠ 0 := by exact_mod_cast (by omega : muZero n ≠ 0)
  simp only [Function.comp_def, scheduleFactor, Nat.cast_pow, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, Real.log_pow]
  have hmu : (mu n : ℝ) = (blockCount (inputBits n) : ℝ) * muZero n := by
    simp [mu, totalSize, muZero]
  rw [hmu]
  field_simp
end ThreeSum.Scales
