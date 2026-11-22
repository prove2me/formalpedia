-- Prove2me | solution 1 for PebblingLean.Hypercube.hasHighDemandDistribution_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:22.967719+00:00
-- url     : https://prove2.me/submissions/c33d65ac-2de0-440f-8faf-0bd3576bbdbc

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Theorems.Thm_PebblingLean_Hypercube_size_constantDistribution
public import Theorems.Thm_PebblingLean_Hypercube_solvableAtLeast_constantDistribution
public import Theorems.Thm_PebblingLean_Hypercube_minOccupiedPileSize_constantDistribution

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
namespace PebblingLean.Hypercube
theorem _root_.solution (n S : ℕ) :
    HasHighDemandDistribution n S (2 ^ n * S) S := by
  exact ⟨constantDistribution n S, by rw [size_constantDistribution],
    solvableAtLeast_constantDistribution n S,
    minOccupiedPileSize_constantDistribution n S⟩
end PebblingLean.Hypercube
