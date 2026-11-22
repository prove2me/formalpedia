-- Prove2me | solution 1 for PebblingLean.Hypercube.hasHighDemandDistribution_split_product_of_optimized_chord_fiber_variable_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:13:19.024462+00:00
-- url     : https://prove2.me/submissions/cd7f1c12-cbfe-48f2-9adf-698ada912fdf

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Theorems.Thm_PebblingLean_Hypercube_HasHighDemandDistribution_mono_cost
public import Theorems.Thm_PebblingLean_Hypercube_HasHighDemandDistribution_mono_minPile
public import Theorems.Thm_PebblingLean_Hypercube_hasHighDemandDistribution_of_optimized_chord_annulusMean_log_of_mean_gap
public import Theorems.Thm_PebblingLean_Hypercube_hasHighDemandDistribution_split_product_of_highDemand_variable


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {a m Tbase costBound S K rIn rOut minNext : ℕ}
    {N : ℕ → ℕ} {gap : ℕ → ℝ}
    (hTbase : 1 ≤ Tbase)
    (hbase : HasHighDemandDistribution m Tbase costBound S)
    (hgap_pos :
      ∀ t : ℕ, S ≤ t → 0 < gap t)
    (hmean :
      ∀ t : ℕ, S ≤ t →
        (t : ℝ) + gap t ≤
          (N t : ℝ) * (annulusMean a rIn rOut : ℝ))
    (hlog :
      ∀ t : ℕ, S ≤ t →
        ((a + 1 : ℕ) : ℝ) * Real.log 2 ≤
          (gap t) ^ 2 /
            (4 * (2 ^ (rOut - rIn) : ℝ) *
              ((N t : ℝ) * (annulusMean a rIn rOut : ℝ))))
    (hfiberCost :
      ∀ t : ℕ, S ≤ t → N t * 2 ^ rOut ≤ t * K)
    (hminNext : minNext ≤ 2 ^ rOut) :
    HasHighDemandDistribution (a + m) 1 (costBound * K) minNext := by
  refine
    hasHighDemandDistribution_split_product_of_highDemand_variable
      (a := a) (m := m) (Tbase := Tbase) (costBound := costBound)
      (S := S) (K := K) (Snew := minNext)
      hTbase hbase ?_
  intro t ht
  have hfiber_raw :
      HasHighDemandDistribution a t (N t * 2 ^ rOut) (2 ^ rOut) :=
    hasHighDemandDistribution_of_optimized_chord_annulusMean_log_of_mean_gap
      (n := a) (N := N t) (rIn := rIn) (rOut := rOut)
      (T := t) (gap := gap t)
      (hgap_pos t ht) (hmean t ht) (hlog t ht)
  exact (hfiber_raw.mono_cost (hfiberCost t ht)).mono_minPile hminNext
end PebblingLean.Hypercube
