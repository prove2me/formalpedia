-- Prove2me | solution 1 for PebblingLean.Hypercube.Paper.lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:15:59.332087+00:00
-- url     : https://prove2.me/submissions/a9986e43-f319-4c91-af5a-e0101b6d6ae7

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Paper
public import Theorems.Thm_PebblingLean_Hypercube_Paper_isOptimalNumber_optimalPebblingNumber
public import Theorems.Thm_PebblingLean_Hypercube_lower_bound_of_isOptimalNumber


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.Paper
open Pebbling
namespace PebblingLean.Hypercube.Paper
theorem _root_.solution (n : ℕ) :
    ((4 : ℚ) / 3) ^ n ≤ (optimalPebblingNumber n : ℚ) :=
  lower_bound_of_isOptimalNumber
    (isOptimalNumber_optimalPebblingNumber n)
end PebblingLean.Hypercube.Paper
