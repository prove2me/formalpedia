-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_chernoffTails_widthBound_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:37:52.005478+00:00
-- url     : https://prove2.me/submissions/dd45bf14-8a14-426d-9dcc-aa6ed6c5ed7c

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_binomialTails_widthBound_finiteBase
public import Theorems.Thm_PebblingLean_Hypercube_binomialLeftTailProbThird_le_chernoff
public import Theorems.Thm_PebblingLean_Hypercube_binomialRightTailProbThird_le_chernoff


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
    (hchernoff :
      ∀ n : ℕ, n0 ≤ n →
        Real.exp (lamLeft n * (rIn A K n : ℝ)) *
            (((1 : ℝ) / 3) * Real.exp (-(lamLeft n)) + ((2 : ℝ) / 3)) ^
              splitA K n +
          Real.exp (-(lamRight n * (rOut A K n : ℝ))) *
            (((1 : ℝ) / 3) * Real.exp (lamRight n) + ((2 : ℝ) / 3)) ^
              splitA K n ≤
        loss n / 8)
    (hlogWidth :
      ∀ n : ℕ, n0 ≤ n →
        ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (loss n) ^ 2 * (minPile (splitM K n) : ℝ) /
            (128 * (2 ^ (2 * annulusWidth A K n) : ℝ)))
    (hstackMin :
      ∀ n : ℕ, n0 ≤ n →
        (2 ^ rOut A K n : ℝ) ≤
          (loss n / 2) * (minPile (splitM K n) : ℝ) *
            (((4 : ℝ) / 3) ^ splitA K n))
    (hceilSlack :
      ∀ n : ℕ, n0 ≤ n →
        1 ≤ loss n * (((4 : ℝ) / 3) ^ splitA K n)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) :=
  hasRealUpperBound_of_recursiveCostBound_binomialTails_widthBound_finiteBase
    (K := K) (A := A) (n0 := n0)
    hn0_pos
    hquarter
    (fun n hn => by
      have hleft :=
        binomialLeftTailProbThird_le_chernoff
          (splitA K n) (rIn A K n) (hlamLeft n hn)
      have hright :=
        binomialRightTailProbThird_le_chernoff
          (splitA K n) (rOut A K n) (hlamRight n hn)
      linarith [hchernoff n hn])
    hlogWidth
    hstackMin
    hceilSlack
end PebblingLean.Hypercube.PaperParameters
