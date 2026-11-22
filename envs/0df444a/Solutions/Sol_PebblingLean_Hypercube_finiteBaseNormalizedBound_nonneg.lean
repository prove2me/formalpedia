-- Prove2me | solution 1 for PebblingLean.Hypercube.finiteBaseNormalizedBound_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:58:09.87684+00:00
-- url     : https://prove2.me/submissions/baad5a7a-9361-411a-983d-a0cce0b203b0

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
theorem _root_.solution (costBound : ℕ → ℕ) (n0 : ℕ) :
    0 ≤ finiteBaseNormalizedBound costBound n0 := by
  unfold finiteBaseNormalizedBound
  exact Finset.sum_nonneg fun n _hn => normalizedCost_nonneg costBound n
end PebblingLean.Hypercube
