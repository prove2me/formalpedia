-- Prove2me | solution 1 for PebblingLean.Hypercube.binomialWindowProbThird_lower_of_tails_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:05:51.359805+00:00
-- url     : https://prove2.me/submissions/0bdb3a15-0da8-4147-a0c3-8cb493140d62

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_binomialWindowProbThird_add_tails_eq_one

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution
    {n rIn rOut : ℕ} {eps : ℝ} (hr : rIn ≤ rOut)
    (htails :
      binomialLeftTailProbThird n rIn +
          binomialRightTailProbThird n rOut ≤ eps) :
    1 - eps ≤ binomialWindowProbThird n rIn rOut := by
  have hpartition := binomialWindowProbThird_add_tails_eq_one n rIn rOut hr
  linarith
end PebblingLean.Hypercube
