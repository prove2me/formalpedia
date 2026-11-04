-- Prove2me | solution 1 for ThreeSum.Scales.log_difference_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:49:41.609075+00:00
-- url     : https://prove2.me/submissions/9d42d145-72ef-4fb4-88cb-de0fae34a9ad

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
import Theorems.Thm_ThreeSum_Scales_input_log_le_bits_add_one

set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section
namespace ThreeSum.Scales
theorem _root_.solution (k : ℕ) {n : ℕ} (hn : 0 < n) :
    Real.log (3 * n ^ k : ℝ) ≤ ((k : ℝ) + 2) * (inputBits n + 1) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity), Real.log_pow]
  have hthree : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h
    exact h
  have hprod := mul_le_mul_of_nonneg_left (input_log_le_bits_add_one hn) (Nat.cast_nonneg k)
  have hm : (0 : ℝ) ≤ inputBits n := Nat.cast_nonneg _
  nlinarith [hm]
end ThreeSum.Scales
