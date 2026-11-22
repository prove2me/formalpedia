-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_annulusBounds_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:32:40.498535+00:00
-- url     : https://prove2.me/submissions/6b8d3060-7cc0-4c62-a6d7-cb19def9c912

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_le_one_of_pos
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_threshold_for_all_demands_of_minPile
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_sampleCountForDemand_mean_upper_of_annulusMean_upper
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_simplifiedBernstein_finiteBase

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
    (hannulusLower :
      ∀ n : ℕ, n0 ≤ n →
        (1 - loss n / 8) * (2 ^ rOut A K n : ℝ) *
            (((3 : ℝ) / 4) ^ splitA K n) ≤
          (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))
    (hannulusUpper :
      ∀ n : ℕ, n0 ≤ n →
        (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ) ≤
          (2 ^ rOut A K n : ℝ) * (((3 : ℝ) / 4) ^ splitA K n))
    (hlogSimple :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
            (loss n) ^ 2 * (t : ℝ) /
              (128 * (2 ^ (rOut A K n - rIn A K n) : ℝ)))
    (hstackMin :
      ∀ n : ℕ, n0 ≤ n →
        (2 ^ rOut A K n : ℝ) ≤
          (loss n / 2) * (minPile (splitM K n) : ℝ) *
            (((4 : ℝ) / 3) ^ splitA K n))
    (hminExp :
      ∀ n : ℕ, n0 ≤ n → n / 5 ≤ rOut A K n)
    (hceilSlack :
      ∀ n : ℕ, n0 ≤ n →
        1 ≤ loss n * (((4 : ℝ) / 3) ^ splitA K n)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) :=
  hasRealUpperBound_of_recursiveCostBound_simplifiedBernstein_finiteBase
    (K := K) (A := A) (n0 := n0)
    hn0_pos
    hquarter
    hannulusLower
    (fun n hn t ht =>
      sampleCountForDemand_mean_upper_of_annulusMean_upper
        (loss_le_one_of_pos (lt_of_lt_of_le hn0_pos hn))
        (hannulusUpper n hn)
        (stack_threshold_for_all_demands_of_minPile (hstackMin n hn) t ht))
    hlogSimple
    hstackMin
    hminExp
    hceilSlack
end PebblingLean.Hypercube.PaperParameters
