-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_binomialTails_widthBound_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:36:57.383508+00:00
-- url     : https://prove2.me/submissions/9a01d60c-2faa-41ac-8f0b-9dc971a6594f

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_rIn_le_rOut
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_binomialWindow_widthBound_finiteBase
public import Theorems.Thm_PebblingLean_Hypercube_binomialWindowProbThird_lower_of_tails_le


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {K A : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hquarter :
      ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n)
    (htails :
      ∀ n : ℕ, n0 ≤ n →
        binomialLeftTailProbThird (splitA K n) (rIn A K n) +
            binomialRightTailProbThird (splitA K n) (rOut A K n) ≤
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
  hasRealUpperBound_of_recursiveCostBound_binomialWindow_widthBound_finiteBase
    (K := K) (A := A) (n0 := n0)
    hn0_pos
    hquarter
    (fun n hn =>
      binomialWindowProbThird_lower_of_tails_le
        (rIn_le_rOut (A := A) (K := K) (n := n))
        (htails n hn))
    hlogWidth
    hstackMin
    hceilSlack
end PebblingLean.Hypercube.PaperParameters
