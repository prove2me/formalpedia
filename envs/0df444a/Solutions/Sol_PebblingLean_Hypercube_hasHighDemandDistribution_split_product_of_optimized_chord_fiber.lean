-- Prove2me | solution 1 for PebblingLean.Hypercube.hasHighDemandDistribution_split_product_of_optimized_chord_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:13:18.528509+00:00
-- url     : https://prove2.me/submissions/8027cc43-f4d0-440f-9168-64a49f3e2caa

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Theorems.Thm_PebblingLean_Hypercube_HasHighDemandDistribution_mono_cost
public import Theorems.Thm_PebblingLean_Hypercube_hasHighDemandDistribution_of_optimized_chord_annulusMean_log_of_mean_gap
public import Theorems.Thm_PebblingLean_Hypercube_hasHighDemandDistribution_split_product_of_highDemand


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {a m Tbase costBound S K N rIn rOut : ℕ} {gap : ℝ}
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
    (hfiberCost : N * 2 ^ rOut ≤ S * K) :
    HasHighDemandDistribution (a + m) 1 (costBound * K) (2 ^ rOut) := by
  have hfiber_raw :
      HasHighDemandDistribution a costBound (N * 2 ^ rOut) (2 ^ rOut) :=
    hasHighDemandDistribution_of_optimized_chord_annulusMean_log_of_mean_gap
      (n := a) (N := N) (rIn := rIn) (rOut := rOut)
      (T := costBound) (gap := gap)
      hgap_pos hmean hlog
  have hfiber : HasHighDemandDistribution a costBound (S * K) (2 ^ rOut) :=
    hfiber_raw.mono_cost hfiberCost
  exact hasHighDemandDistribution_split_product_of_highDemand
    (a := a) (m := m) (Tbase := Tbase)
    (costBound := costBound) (S := S) (K := K) (Snew := 2 ^ rOut)
    hTbase hbase hfiber
end PebblingLean.Hypercube
