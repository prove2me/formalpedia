-- Prove2me | solution 1 for PebblingLean.Hypercube.hasHighDemandDistribution_split_product_of_optimized_chord_fiber_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:47.101886+00:00
-- url     : https://prove2.me/submissions/67f2363e-8210-4a43-96cf-d09f90ae2e80

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Theorems.Thm_PebblingLean_Hypercube_hasHighDemandDistribution_split_product_of_optimized_chord_fiber
public import Theorems.Thm_PebblingLean_Hypercube_HasHighDemandDistribution_mono_minPile


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {a m Tbase costBound S K N rIn rOut minNext : ℕ} {gap : ℝ}
    (hTbase : 1 ≤ Tbase)
    (hbase : HasHighDemandDistribution m Tbase costBound S)
    (hgap_pos : 0 < gap)
    (hmean :
      (costBound : ℝ) + gap ≤
        (N : ℝ) * (annulusMean a rIn rOut : ℝ))
    (hlog :
      ((a + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean a rIn rOut : ℝ))))
    (hfiberCost : N * 2 ^ rOut ≤ S * K)
    (hminNext : minNext ≤ 2 ^ rOut) :
    HasHighDemandDistribution (a + m) 1 (costBound * K) minNext :=
  (hasHighDemandDistribution_split_product_of_optimized_chord_fiber
    (a := a) (m := m) (Tbase := Tbase) (costBound := costBound)
    (S := S) (K := K) (N := N) (rIn := rIn) (rOut := rOut)
    (gap := gap) hTbase hbase hgap_pos hmean hlog hfiberCost).mono_minPile
      hminNext
end PebblingLean.Hypercube
