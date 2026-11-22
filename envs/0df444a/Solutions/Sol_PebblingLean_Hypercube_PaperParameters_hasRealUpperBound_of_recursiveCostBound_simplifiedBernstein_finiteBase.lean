-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_simplifiedBernstein_finiteBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:31:54.809666+00:00
-- url     : https://prove2.me/submissions/be0b84d2-bd68-4b4a-aa3e-65049bfab85f

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_one_le_minPile
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_loss_le_two_of_pos
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_demandGapForDemand_pos
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_sampleCountForDemand_mean_of_annulusMean_lower
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_condition_of_mean_upper
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_annulusMeanLower_finiteBase

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
    (hmeanUpper :
      ∀ n : ℕ, n0 ≤ n →
        ∀ t : ℕ, minPile (splitM K n) ≤ t →
          (sampleCountForDemand A K n t : ℝ) *
            (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ) ≤
              2 * (t : ℝ))
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
  hasRealUpperBound_of_recursiveCostBound_annulusMeanLower_finiteBase
    (K := K) (A := A) (n0 := n0)
    hn0_pos
    hquarter
    hannulus
    (fun n hn t ht => by
      have ht_pos : 0 < t :=
        lt_of_lt_of_le Nat.zero_lt_one ((one_le_minPile (splitM K n)).trans ht)
      have hgap_pos :
          0 < demandGapForDemand n t :=
        demandGapForDemand_pos (lt_of_lt_of_le hn0_pos hn) ht_pos
      have hmean_lower :
          (t : ℝ) + demandGapForDemand n t ≤
            (sampleCountForDemand A K n t : ℝ) *
              (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ) :=
        sampleCountForDemand_mean_of_annulusMean_lower
          (loss_le_two_of_pos (lt_of_lt_of_le hn0_pos hn))
          (hannulus n hn)
      have hmu_pos :
          0 < (sampleCountForDemand A K n t : ℝ) *
            (annulusMean (splitA K n) (rIn A K n) (rOut A K n) : ℝ) := by
        have ht_real_pos : 0 < (t : ℝ) := by exact_mod_cast ht_pos
        have hlhs_pos : 0 < (t : ℝ) + demandGapForDemand n t :=
          add_pos_of_pos_of_nonneg ht_real_pos hgap_pos.le
        exact lt_of_lt_of_le hlhs_pos hmean_lower
      exact log_condition_of_mean_upper
        (A := A) (K := K) (n := n) (t := t)
        ht_pos hmu_pos (hmeanUpper n hn t ht) (hlogSimple n hn t ht))
    hstackMin
    hminExp
    hceilSlack
end PebblingLean.Hypercube.PaperParameters
