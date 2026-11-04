-- Prove2me | solution 1 for ThreeSum.Scales.typedOutputs_log_ratio_tendsto_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:21:50.34138+00:00
-- url     : https://prove2.me/submissions/0b2e8b7e-b523-4ca6-a6c6-45334b3bd773

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
import Theorems.Thm_ThreeSum_BinomialEntropy_output_table_rate
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
    Tendsto (fun n : ℕ => Real.log (typedOutputs n : ℝ) / Real.log n) atTop
      (𝓝 (2 * Parameters.E / 5)) := by
  have hl := BinomialEntropy.output_table_rate.comp muZero_tendsto_atTop
  have hs := mu_log_ratio_tendsto.const_mul (Real.log 2)
  have h := hl.mul hs
  have hlim : 2 * Parameters.E * (Real.log 2 * (1 / (5 * Real.log 2))) =
      2 * Parameters.E / 5 := by field_simp
  rw [hlim] at h
  apply h.congr'
  filter_upwards [muZero_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (muZero n : ℝ) ≠ 0 := by exact_mod_cast (by omega : muZero n ≠ 0)
  simp only [Function.comp_def, typedOutputs, Nat.cast_pow, Real.log_pow]
  have hmu : (mu n : ℝ) = (blockCount (inputBits n) : ℝ) * muZero n := by
    simp [mu, totalSize, muZero]
  rw [hmu]
  field_simp
end ThreeSum.Scales
