-- Prove2me | solution 1 for PebblingLean.Hypercube.weightedSphereSum_half_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:04.484328+00:00
-- url     : https://prove2.me/submissions/77453b42-ecfd-45d8-b52b-d0f2223ec8da

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
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) * ((1 : ℝ) / 2) ^ i) =
      ((3 : ℝ) / 2) ^ n := by
  have h := add_pow ((1 : ℝ) / 2) (1 : ℝ) n
  calc
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) * ((1 : ℝ) / 2) ^ i)
        = ∑ i ∈ Finset.range (n + 1),
            ((1 : ℝ) / 2) ^ i * 1 ^ (n - i) * (Nat.choose n i : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
    _ = (((1 : ℝ) / 2) + 1) ^ n := h.symm
    _ = ((3 : ℝ) / 2) ^ n := by norm_num
end PebblingLean.Hypercube
