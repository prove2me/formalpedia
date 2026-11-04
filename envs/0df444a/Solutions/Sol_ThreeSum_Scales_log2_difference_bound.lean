-- Prove2me | solution 1 for ThreeSum.Scales.log2_difference_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:53:26.409121+00:00
-- url     : https://prove2.me/submissions/71d8b277-2a4f-438b-a3a2-c299e3648672

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
import Theorems.Thm_ThreeSum_Scales_log_difference_bound
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Parameters_log_two_lower
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution (k : ℕ) {n : ℕ} (hn : 0 < n) :
    Nat.log2 (3 * n ^ k) ≤ 2 * (k + 2) * (inputBits n + 1) := by
  have hl : (Nat.log2 (3 * n ^ k) : ℝ) ≤ Real.log (3 * n ^ k : ℝ) / Real.log 2 := by
    simpa [Nat.log2_eq_log_two, Real.logb] using Real.natLog_le_logb (3 * n ^ k) 2
  have hmul := (le_div_iff₀ Parameters.log_two_pos).mp hl
  have hdiff := log_difference_bound k hn
  have hk : (0 : ℝ) ≤ Nat.log2 (3 * n ^ k) := Nat.cast_nonneg _
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Parameters.log_two_lower; linarith
  have hhalf := mul_le_mul_of_nonneg_left hlog hk
  have hR : (Nat.log2 (3 * n ^ k) : ℝ) ≤ 2 * ((k : ℝ) + 2) * (inputBits n + 1) := by
    nlinarith [hhalf]
  exact_mod_cast hR
end ThreeSum.Scales
