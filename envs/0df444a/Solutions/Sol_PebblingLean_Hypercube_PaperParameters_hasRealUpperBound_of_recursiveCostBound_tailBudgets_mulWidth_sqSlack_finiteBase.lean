-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_tailBudgets_mulWidth_sqSlack_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:40:26.174796+00:00
-- url     : https://prove2.me/submissions/23259938-ded4-4779-b489-0dbe72a399e1

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_logWidth_of_mul_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_tailBudgets_widthBound_sqSlack_finiteBase

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {K A : ℝ} {n0 : ℕ} {lamLeft lamRight : ℕ → ℝ}
    (hn0_pos : 0 < n0)
    (hquarter :
      ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n)
    (hlamLeft :
      ∀ n : ℕ, n0 ≤ n → 0 ≤ lamLeft n)
    (hlamRight :
      ∀ n : ℕ, n0 ≤ n → 0 ≤ lamRight n)
    (hleft :
      ∀ n : ℕ, n0 ≤ n →
        Real.exp (lamLeft n * (rIn A K n : ℝ)) *
            (((1 : ℝ) / 3) * Real.exp (-(lamLeft n)) + ((2 : ℝ) / 3)) ^
              splitA K n ≤
        loss n / 16)
    (hright :
      ∀ n : ℕ, n0 ≤ n →
        Real.exp (-(lamRight n * (rOut A K n : ℝ))) *
            (((1 : ℝ) / 3) * Real.exp (lamRight n) + ((2 : ℝ) / 3)) ^
              splitA K n ≤
        loss n / 16)
    (hlogWidthMul :
      ∀ n : ℕ, n0 ≤ n →
        128 * (2 ^ (2 * annulusWidth A K n) : ℝ) *
            (((splitA K n + 1 : ℕ) : ℝ) * Real.log 2) ≤
          (loss n) ^ 2 * (minPile (splitM K n) : ℝ))
    (hstackMin :
      ∀ n : ℕ, n0 ≤ n →
        (2 ^ rOut A K n : ℝ) ≤
          (loss n / 2) * (minPile (splitM K n) : ℝ) *
            (((4 : ℝ) / 3) ^ splitA K n))
    (hceilSq :
      ∀ n : ℕ, n0 ≤ n →
        (n : ℝ) ^ 2 ≤ (((4 : ℝ) / 3) ^ splitA K n)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) :=
  hasRealUpperBound_of_recursiveCostBound_tailBudgets_widthBound_sqSlack_finiteBase
    (K := K) (A := A) (n0 := n0)
    hn0_pos hquarter hlamLeft hlamRight hleft hright
    (fun n hn => logWidth_of_mul_le (hlogWidthMul n hn))
    hstackMin
    hceilSq
end PebblingLean.Hypercube.PaperParameters
