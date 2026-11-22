-- Prove2me | solution 1 for PebblingLean.Hypercube.binomialMassThird_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:47.651173+00:00
-- url     : https://prove2.me/submissions/d35a8de0-118f-4199-b723-06136ea2ba7d

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution (n i : ℕ) :
    0 ≤ binomialMassThird n i := by
  unfold binomialMassThird
  positivity
end PebblingLean.Hypercube
