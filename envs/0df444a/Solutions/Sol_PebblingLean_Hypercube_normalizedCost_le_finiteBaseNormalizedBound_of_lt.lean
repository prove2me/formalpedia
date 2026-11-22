-- Prove2me | solution 1 for PebblingLean.Hypercube.normalizedCost_le_finiteBaseNormalizedBound_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:06:24.776008+00:00
-- url     : https://prove2.me/submissions/a0e78844-2620-4bf5-8e99-67309e72b584

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Theorems.Thm_PebblingLean_Hypercube_normalizedCost_nonneg

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    (costBound : ℕ → ℕ) {n0 n : ℕ} (hn : n < n0) :
    normalizedCost costBound n ≤ finiteBaseNormalizedBound costBound n0 := by
  unfold finiteBaseNormalizedBound
  exact Finset.single_le_sum
    (fun m _hm => normalizedCost_nonneg costBound m)
    (Finset.mem_range.mpr hn)
end PebblingLean.Hypercube
