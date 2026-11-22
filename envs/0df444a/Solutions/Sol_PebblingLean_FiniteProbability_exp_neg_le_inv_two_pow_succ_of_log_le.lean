-- Prove2me | solution 1 for PebblingLean.FiniteProbability.exp_neg_le_inv_two_pow_succ_of_log_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:55.895847+00:00
-- url     : https://prove2.me/submissions/393dc1c8-3959-44a2-ae2c-7f6bbf4ba451

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Concentration

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω : Type*}
namespace PebblingLean.FiniteProbability
theorem _root_.solution (n : ℕ) {exponent : ℝ}
    (hlog : ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤ exponent) :
    Real.exp (-exponent) ≤
      (((1 : ℚ) / (2 ^ (n + 1) : ℚ) : ℚ) : ℝ) := by
  have hfirst :
      Real.exp (-exponent) ≤
        Real.exp (-(((n + 1 : ℕ) : ℝ) * Real.log 2)) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hlog)
  have heq :
      Real.exp (-(((n + 1 : ℕ) : ℝ) * Real.log 2)) =
        (((1 : ℚ) / (2 ^ (n + 1) : ℚ) : ℚ) : ℝ) := by
    calc
      Real.exp (-(((n + 1 : ℕ) : ℝ) * Real.log 2))
          = (Real.exp ((((n + 1 : ℕ) : ℝ) * Real.log 2)))⁻¹ := by
            rw [Real.exp_neg]
      _ = ((2 : ℝ) ^ (n + 1))⁻¹ := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = (((1 : ℚ) / (2 ^ (n + 1) : ℚ) : ℚ) : ℝ) := by
            simp_all
  exact hfirst.trans_eq heq
end PebblingLean.FiniteProbability
