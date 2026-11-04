-- Prove2me | solution 1 for ThreeSum.Scales.radix_log_ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:34:19.829381+00:00
-- url     : https://prove2.me/submissions/96d7e938-accd-4c7d-a188-54ec789ba931

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
import Theorems.Thm_ThreeSum_Scales_mu_log_ratio_tendsto
import Theorems.Thm_ThreeSum_Scales_microHalf_tendsto_atTop
import Theorems.Thm_ThreeSum_Scales_localPrime_log_rate
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
    Tendsto (fun n : ℕ => Real.log (radix n : ℝ) / Real.log n) atTop
      (𝓝 ((Parameters.E + 1 / 2) / 5)) := by
  have hl := localPrime_log_rate.comp (microHalf_tendsto_atTop.comp inputBits_tendsto_atTop)
  have hs := mu_log_ratio_tendsto.const_mul (Real.log 2)
  have h := hl.mul hs
  have hlim : (Parameters.E + 1 / 2) * (Real.log 2 * (1 / (5 * Real.log 2))) =
      (Parameters.E + 1 / 2) / 5 := by field_simp
  rw [hlim] at h
  apply h.congr'
  filter_upwards [(microHalf_tendsto_atTop.comp inputBits_tendsto_atTop).eventually
      (eventually_ge_atTop 1)] with n hn
  change 1 ≤ microHalf (inputBits n) at hn
  have hn0 : (microHalf (inputBits n) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : microHalf (inputBits n) ≠ 0)
  simp only [Function.comp_def, radix, Nat.cast_pow, Real.log_pow, localRadix]
  have hmu : (mu n : ℝ) = (blockCount (inputBits n) : ℝ) *
      (2 * microHalf (inputBits n)) := by simp [mu, totalSize, microSize, microHalf]
  rw [hmu]
  field_simp
end ThreeSum.Scales
