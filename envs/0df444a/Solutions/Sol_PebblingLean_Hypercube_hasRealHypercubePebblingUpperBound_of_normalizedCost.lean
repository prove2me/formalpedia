-- Prove2me | solution 1 for PebblingLean.Hypercube.hasRealHypercubePebblingUpperBound_of_normalizedCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:28.873514+00:00
-- url     : https://prove2.me/submissions/807bffca-aa80-4299-abaf-3c78a2d16f66

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Theorems.Thm_PebblingLean_Hypercube_costBound_le_of_normalizedCost_le

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {costBound : ℕ → ℕ} {C : ℝ}
    (hupper : HasHypercubePebblingUpperBound costBound)
    (hnorm : ∀ n : ℕ, normalizedCost costBound n ≤ C) :
    HasRealHypercubePebblingUpperBound C := by
  intro n
  exact ⟨costBound n, hupper n,
    costBound_le_of_normalizedCost_le hnorm n⟩
end PebblingLean.Hypercube
