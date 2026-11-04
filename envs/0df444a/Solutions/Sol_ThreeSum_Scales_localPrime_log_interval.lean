-- Prove2me | solution 1 for ThreeSum.Scales.localPrime_log_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:22.022615+00:00
-- url     : https://prove2.me/submissions/1ccbbb95-9f74-4312-8e35-a13c12251dc2

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
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_sq_lower
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_sq_upper
import Theorems.Thm_ThreeSum_LocalCoverBounds_localThreshold_pos
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution (h : ℕ) :
    Real.log (LocalCoverBounds.localThreshold h : ℝ) ≤
      2 * Real.log (LocalCoverBounds.localPrime h : ℝ) ∧
    2 * Real.log (LocalCoverBounds.localPrime h : ℝ) ≤
      Real.log 16 + Real.log (LocalCoverBounds.localThreshold h : ℝ) := by
  have hN : (0 : ℝ) < LocalCoverBounds.localThreshold h := by
    exact_mod_cast LocalCoverBounds.localThreshold_pos h
  have hp : (0 : ℝ) < LocalCoverBounds.localPrime h := by
    exact_mod_cast LocalCoverBounds.localPrime_pos h
  have hl : (LocalCoverBounds.localThreshold h : ℝ) ≤
      (LocalCoverBounds.localPrime h : ℝ) ^ 2 := by
    exact_mod_cast LocalCoverBounds.localPrime_sq_lower h
  have hu : (LocalCoverBounds.localPrime h : ℝ) ^ 2 ≤
      16 * (LocalCoverBounds.localThreshold h : ℝ) := by
    exact_mod_cast LocalCoverBounds.localPrime_sq_upper h
  constructor
  · simpa [Real.log_pow] using Real.log_le_log hN hl
  · simpa [Real.log_pow, Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hN.ne'] using
      Real.log_le_log (by positivity : (0 : ℝ) < (LocalCoverBounds.localPrime h : ℝ) ^ 2) hu
end ThreeSum.Scales
