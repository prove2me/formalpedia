-- Prove2me | solution 1 for ThreeSum.Scales.input_log_le_bits_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:23.128839+00:00
-- url     : https://prove2.me/submissions/95920b61-ddb9-42b4-99f4-c697916a00f2

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
import Theorems.Thm_ThreeSum_Parameters_log_two_upper
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) ≤ inputBits n + 1 := by
  have hpow : n ≤ 2 ^ (inputBits n + 1) := by
    simpa [inputBits, Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpowR : (n : ℝ) ≤ (2 : ℝ) ^ (inputBits n + 1) := by exact_mod_cast hpow
  have hl := Real.log_le_log hnpos hpowR
  rw [Real.log_pow] at hl
  have htwo : Real.log 2 ≤ 1 := by have := Parameters.log_two_upper; linarith
  have hm : (0 : ℝ) ≤ inputBits n + 1 := by positivity
  exact hl.trans (by simpa using mul_le_of_le_one_right hm htwo)
end ThreeSum.Scales
