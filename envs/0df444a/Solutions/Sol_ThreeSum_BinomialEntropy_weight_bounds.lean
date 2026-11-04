-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.weight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:50:23.162843+00:00
-- url     : https://prove2.me/submissions/2da303f2-6794-4f79-a4ac-36981bc22589

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Theorems.Thm_ThreeSum_BinomialEntropy_weight_nonneg
import Theorems.Thm_ThreeSum_BinomialEntropy_weight_mode
import Theorems.Thm_ThreeSum_BinomialEntropy_sum_weight

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.BinomialEntropy
open Finset Real Set Filter
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.BinomialEntropy
theorem _root_.solution {n k : ℕ} (hk : k < n) :
    weight n k k ≤ (n : ℝ) ^ n ∧
      (n : ℝ) ^ n ≤ (n + 1 : ℝ) * weight n k k := by
  constructor
  · rw [← sum_weight hk.le]
    exact single_le_sum (fun j _ => weight_nonneg n k j) (mem_range.mpr (by omega))
  · rw [← sum_weight hk.le]
    calc
      _ ≤ ∑ _j ∈ range (n + 1), weight n k k := sum_le_sum (fun _ _ => weight_mode hk)
      _ = _ := by simp
end ThreeSum.BinomialEntropy
