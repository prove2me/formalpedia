-- Prove2me | solution 1 for PebblingLean.Hypercube.binomialWindowProbThird_add_tails_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:04:51.795612+00:00
-- url     : https://prove2.me/submissions/dc9af718-b7a6-429f-956e-1308d8bc57d4

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
public import Theorems.Thm_PebblingLean_Hypercube_binomialTotalProbThird_eq_one
public import Theorems.Thm_PebblingLean_Hypercube_binomialWindow_tail_partition_term

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability
namespace PebblingLean.Hypercube
theorem _root_.solution
    (n rIn rOut : ℕ) (hr : rIn ≤ rOut) :
    binomialWindowProbThird n rIn rOut +
        binomialLeftTailProbThird n rIn +
          binomialRightTailProbThird n rOut = 1 := by
  rw [← binomialTotalProbThird_eq_one n]
  unfold binomialWindowProbThird binomialLeftTailProbThird binomialRightTailProbThird
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  unfold binomialMassThird
  have hterm := binomialWindow_tail_partition_term (n := n) (rIn := rIn)
    (rOut := rOut) (i := i) hr
  unfold binomialMassThird at hterm
  exact hterm
end PebblingLean.Hypercube
