-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_annulusMeanLower_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:18:49.826705+00:00
-- url     : https://prove2.me/submissions/a2c38e60-f5fc-4446-b171-2f3400099bdc

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_le_two_of_pos
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_sampleCountForDemand_mean_of_annulusMean_lower
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_threshold_for_all_demands_of_minPile
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_concreteSample_ceiling_finiteBase

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
    (hannulus :
      ∀ n : ℕ, n0 ≤ n →
        (1 - loss n / 8) * (2 ^ rOut A K n : ℝ) *
            (((3 : ℝ) / 4) ^ splitA K n) ≤
          (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))
    (hlog :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          ((splitA K n + 1 : ℕ) : ℝ) * Real.log 2 ≤
            (demandGapForDemand n t) ^ 2 /
              (4 * (2 ^ (rOut A K n - rIn A K n) : ℝ) *
                ((sampleCountForDemand A K n t : ℝ) *
                  (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ))))
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
  hasRealUpperBound_of_recursiveCostBound_concreteSample_ceiling_finiteBase
    (K := K) (A := A) (n0 := n0)
    hn0_pos
    hquarter
    (fun n hn _t _ht =>
      sampleCountForDemand_mean_of_annulusMean_lower
        (loss_le_two_of_pos (lt_of_lt_of_le hn0_pos hn))
        (hannulus n hn))
    hlog
    (fun n hn => stack_threshold_for_all_demands_of_minPile (hstackMin n hn))
    hminExp
    hceilSlack
end PebblingLean.Hypercube.PaperParameters
