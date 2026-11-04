-- Prove2me | solution 1 for ThreeSum.Scales.mu_log_ratio_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:07:41.858878+00:00
-- url     : https://prove2.me/submissions/3dd8f31d-f72d-4aa1-b183-09f397720a94

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
import Theorems.Thm_ThreeSum_Scales_totalSize_ratio_tendsto
import Theorems.Thm_ThreeSum_Scales_inputBits_tendsto_atTop
import Theorems.Thm_ThreeSum_Scales_inputBits_log_ratio_tendsto
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
    Tendsto (fun n : ℕ => (mu n : ℝ) / Real.log n) atTop
      (𝓝 (1 / (5 * Real.log 2))) := by
  have h := (totalSize_ratio_tendsto.comp inputBits_tendsto_atTop).mul
    inputBits_log_ratio_tendsto
  have hlim : (1 / 5 : ℝ) * (1 / Real.log 2) = 1 / (5 * Real.log 2) := by ring
  rw [hlim] at h
  apply h.congr'
  filter_upwards [inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, mu]
  field_simp
end ThreeSum.Scales
