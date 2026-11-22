-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_binomialWindow_widthBound_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:36:13.101062+00:00
-- url     : https://prove2.me/submissions/e6e0fd01-d29c-41cd-ae81-8a206fdfdd66

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_n_div_five_le_rOut_of_four_mul_le
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusMean_lower_of_binomialWindowProbThird
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_annulusLower_widthBound_finiteBase

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
    (hwindow :
      ∀ n : ℕ, n0 ≤ n →
        1 - loss n / 8 ≤
          binomialWindowProbThird
            (splitA K n) (rIn A K n) (rOut A K n))
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
  hasRealUpperBound_of_recursiveCostBound_annulusLower_widthBound_finiteBase
    (K := K) (A := A) (n0 := n0)
    hn0_pos
    hquarter
    (fun n hn =>
      annulusMean_lower_of_binomialWindowProbThird
        (hwindow n hn))
    hlogWidth
    hstackMin
    (fun n hn => n_div_five_le_rOut_of_four_mul_le (hquarter n hn))
    hceilSlack
end PebblingLean.Hypercube.PaperParameters
