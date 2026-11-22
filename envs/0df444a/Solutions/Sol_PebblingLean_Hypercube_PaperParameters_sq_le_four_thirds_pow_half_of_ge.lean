-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.sq_le_four_thirds_pow_half_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:13:13.920554+00:00
-- url     : https://prove2.me/submissions/54ca4913-983f-4407-a01d-4243c3bf097f

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_sq_growth_step_for_four_thirds_half

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution (n : ℕ) (hn : 58 ≤ n) :
    (n : ℝ) ^ 2 ≤ (((4 : ℝ) / 3) ^ (n / 2)) := by
  induction n using Nat.twoStepInduction with
  | zero => omega
  | one => omega
  | more n ih0 _ih1 =>
      by_cases hnbase : 58 ≤ n
      · have ih := ih0 hnbase
        have hstep := sq_growth_step_for_four_thirds_half n (by omega : 14 ≤ n)
        calc
          ((n + 2 : ℕ) : ℝ) ^ 2 ≤ ((4 : ℝ) / 3) * (n : ℝ) ^ 2 := hstep
          _ ≤ ((4 : ℝ) / 3) * (((4 : ℝ) / 3) ^ (n / 2)) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = ((4 : ℝ) / 3) ^ ((n + 2) / 2) := by
            have hdiv : (n + 2) / 2 = n / 2 + 1 := by omega
            rw [hdiv, pow_succ]
            ring
      · have hcases : n = 56 ∨ n = 57 := by omega
        rcases hcases with rfl | rfl <;> norm_num
end PebblingLean.Hypercube.PaperParameters
