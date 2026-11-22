-- Prove2me | solution 1 for PebblingLean.Hypercube.LossRecurrence.geomSum_le_two_of_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:06:03.826828+00:00
-- url     : https://prove2.me/submissions/a65eb580-b9d9-4019-9486-642c197f15c9

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.LossRecurrence
namespace PebblingLean.Hypercube.LossRecurrence
theorem _root_.solution {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_half : q ≤ (1 : ℝ) / 2) (k : ℕ) :
    geomSum q k ≤ 2 := by
  have hpow :
      ∀ i : ℕ, q ^ i ≤ ((1 : ℝ) / 2) ^ i := by
    intro i
    exact pow_le_pow_left₀ hq_nonneg hq_half i
  have hsum :
      geomSum q k ≤ ∑ i ∈ Finset.range k, ((1 : ℝ) / 2) ^ i := by
    exact Finset.sum_le_sum fun i _hi => hpow i
  exact hsum.trans (sum_geometric_two_le k)
end PebblingLean.Hypercube.LossRecurrence
