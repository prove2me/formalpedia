-- Prove2me | solution 1 for PebblingLean.Hypercube.binomialTotalProbThird_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:09.437122+00:00
-- url     : https://prove2.me/submissions/91a6e740-fe54-425c-aba7-32f525365379

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
theorem _root_.solution (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), binomialMassThird n i) = 1 := by
  have h := add_pow ((1 : ℝ) / 3) ((2 : ℝ) / 3) n
  calc
    (∑ i ∈ Finset.range (n + 1), binomialMassThird n i)
        = ∑ i ∈ Finset.range (n + 1),
            ((1 : ℝ) / 3) ^ i * ((2 : ℝ) / 3) ^ (n - i) *
              (Nat.choose n i : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          unfold binomialMassThird
          ring
    _ = (((1 : ℝ) / 3) + ((2 : ℝ) / 3)) ^ n := h.symm
    _ = 1 := by norm_num
end PebblingLean.Hypercube
