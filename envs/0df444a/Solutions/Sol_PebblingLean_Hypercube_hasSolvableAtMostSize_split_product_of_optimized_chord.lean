-- Prove2me | solution 1 for PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_optimized_chord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:44.417043+00:00
-- url     : https://prove2.me/submissions/7d76508f-d2d2-4958-9f22-9ea0b736720e

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Theorems.Thm_PebblingLean_Hypercube_hasHighDemandDistribution_of_optimized_chord_annulusMean_log_of_mean_gap
public import Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_split_product_of_highDemand


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {a m N rIn rOut Tbase K : ℕ} {gap : ℝ}
    (hTbase : 1 ≤ Tbase)
    (hgap_pos : 0 < gap)
    (hmean :
      (Tbase : ℝ) + gap ≤
        (N : ℝ) * (annulusMean m rIn rOut : ℝ))
    (hlog :
      ((m + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean m rIn rOut : ℝ))))
    (hfiber :
      Pebbling.HasSolvableAtMostSize (graph a)
        (N * 2 ^ rOut) (2 ^ rOut * K)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      ((N * 2 ^ rOut) * K) := by
  have hhigh :
      HasHighDemandDistribution m Tbase (N * 2 ^ rOut) (2 ^ rOut) :=
    hasHighDemandDistribution_of_optimized_chord_annulusMean_log_of_mean_gap
      (n := m) (N := N) (rIn := rIn) (rOut := rOut)
      (T := Tbase) (gap := gap)
      hgap_pos hmean hlog
  exact hasSolvableAtMostSize_split_product_of_highDemand
    (a := a) (m := m) (Tbase := Tbase)
    (costBound := N * 2 ^ rOut) (S := 2 ^ rOut) (K := K)
    hTbase hhigh hfiber
end PebblingLean.Hypercube
