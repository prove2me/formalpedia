-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.log_choose_entropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:21.135209+00:00
-- url     : https://prove2.me/submissions/4dde8c90-0c26-42cc-9218-9b37318bce27

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Theorems.Thm_ThreeSum_BinomialEntropy_log_choose_entropy_bounds_interior

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.BinomialEntropy
open Finset Real Set Filter
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.BinomialEntropy
theorem _root_.solution {n k : ℕ} (hk : k ≤ n) :
    (n : ℝ) * Real.binEntropy ((k : ℝ) / n) - Real.log (n + 1 : ℝ) ≤
        Real.log (n.choose k : ℝ) ∧
      Real.log (n.choose k : ℝ) ≤ (n : ℝ) * Real.binEntropy ((k : ℝ) / n) := by
  have hl : 0 ≤ Real.log (n + 1 : ℝ) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  by_cases hk0 : k = 0
  · subst k
    simp only [Nat.choose_zero_right, Nat.cast_zero, zero_div, Real.binEntropy_zero,
      mul_zero, Nat.cast_one, Real.log_one, zero_sub]
    exact ⟨by linarith, le_rfl⟩
  by_cases hkn : k = n
  · subst k
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hk0
    simp only [Nat.choose_self, div_self hn, Real.binEntropy_one, mul_zero,
      Nat.cast_one, Real.log_one, zero_sub]
    exact ⟨by linarith, le_rfl⟩
  exact log_choose_entropy_bounds_interior (Nat.pos_of_ne_zero hk0) (lt_of_le_of_ne hk hkn)
end ThreeSum.BinomialEntropy
