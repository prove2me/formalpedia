-- Prove2me | solution 1 for PebblingLean.Hypercube.annulusMean_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:02.660824+00:00
-- url     : https://prove2.me/submissions/177a259d-7e13-4446-8e8a-27d8f97308b0

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
theorem _root_.solution (n rIn rOut : ℕ) :
    0 ≤ (annulusMean n rIn rOut : ℝ) := by
  unfold annulusMean annulusMeanNumerator
  positivity
end PebblingLean.Hypercube
