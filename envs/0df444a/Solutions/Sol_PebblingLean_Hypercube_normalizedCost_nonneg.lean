-- Prove2me | solution 1 for PebblingLean.Hypercube.normalizedCost_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:57:27.513981+00:00
-- url     : https://prove2.me/submissions/eb2bf2ce-573a-4de3-9016-7b5529a5cc05

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
namespace PebblingLean.Hypercube
theorem _root_.solution (costBound : ℕ → ℕ) (n : ℕ) :
    0 ≤ normalizedCost costBound n := by
  unfold normalizedCost
  positivity
end PebblingLean.Hypercube
