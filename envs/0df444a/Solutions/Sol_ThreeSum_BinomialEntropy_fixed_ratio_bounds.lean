-- Prove2me | solution 1 for ThreeSum.BinomialEntropy.fixed_ratio_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:03:17.68674+00:00
-- url     : https://prove2.me/submissions/1d1e1a49-d217-4b00-8a31-16996114d579

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Theorems.Thm_ThreeSum_BinomialEntropy_log_choose_entropy_bounds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.BinomialEntropy
open Finset Real Set Filter
open scoped Topology
set_option maxRecDepth 10000
namespace ThreeSum.BinomialEntropy
theorem _root_.solution {c r m : ℕ} (hc : 0 < c) (hr : r ≤ c) (hm : 0 < m) :
    (c : ℝ) * Real.binEntropy ((r : ℝ) / c) - Real.log (c * m + 1 : ℝ) / m ≤
        Real.log ((c * m).choose (r * m) : ℝ) / m ∧
      Real.log ((c * m).choose (r * m) : ℝ) / m ≤
        (c : ℝ) * Real.binEntropy ((r : ℝ) / c) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have h := log_choose_entropy_bounds (Nat.mul_le_mul_right m hr)
  have hp : (((r * m : ℕ) : ℝ) / ((c * m : ℕ) : ℝ)) = (r : ℝ) / c := by
    push_cast
    field_simp
  rw [hp, Nat.cast_mul] at h
  constructor
  · apply (le_div_iff₀ hm').mpr
    have heq : ((c : ℝ) * Real.binEntropy ((r : ℝ) / c) -
        Real.log (c * m + 1 : ℝ) / m) * m =
        (c : ℝ) * m * Real.binEntropy ((r : ℝ) / c) - Real.log (c * m + 1 : ℝ) := by
      field_simp
    rw [heq]
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h.1
  · apply (div_le_iff₀ hm').mpr
    nlinarith [h.2]
end ThreeSum.BinomialEntropy
