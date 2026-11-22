-- Prove2me | solution 1 for PebblingLean.Hypercube.binomialExpNegMomentThird_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:13.204435+00:00
-- url     : https://prove2.me/submissions/d666ccf2-ebcf-4fd0-bcf2-8d83915d0439

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
theorem _root_.solution (n : ℕ) (lam : ℝ) :
    (∑ i ∈ Finset.range (n + 1),
        binomialMassThird n i * (Real.exp (-lam)) ^ i) =
      (((1 : ℝ) / 3) * Real.exp (-lam) + ((2 : ℝ) / 3)) ^ n := by
  have h := add_pow (((1 : ℝ) / 3) * Real.exp (-lam)) ((2 : ℝ) / 3) n
  calc
    (∑ i ∈ Finset.range (n + 1),
        binomialMassThird n i * (Real.exp (-lam)) ^ i)
        = ∑ i ∈ Finset.range (n + 1),
            (((1 : ℝ) / 3) * Real.exp (-lam)) ^ i *
              (((2 : ℝ) / 3) ^ (n - i)) * (Nat.choose n i : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          unfold binomialMassThird
          rw [mul_pow]
          ring
    _ = (((1 : ℝ) / 3) * Real.exp (-lam) + ((2 : ℝ) / 3)) ^ n := h.symm
end PebblingLean.Hypercube
