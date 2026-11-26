-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.sInf_card_add_eq_add_sum_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:25.033052+00:00
-- url     : https://prove2.me/submissions/dad8504a-4f9c-4c38-8c53-230779744c3a

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBoundFunction
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Definitions.Def_SumOfSetsInSeveralDimensions_Construction
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_MinCardAdd
public import Theorems.Thm_SumOfSetsInSeveralDimensions_minCardAdd_eq_sumsetCardLowerBound
public import Theorems.Thm_Finset_affineDim_eq_finrank_span_sub
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_eq


set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {d m n : ℕ}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution (hd : 1 ≤ d) (hm : 1 ≤ m) (hmn : m ≤ n) (hn : d + 1 ≤ n) :
    sInf {k | ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧
      Module.finrank ℝ (Submodule.span ℝ (↑(A + B) - ↑(A + B) : Set (Fin d → ℝ))) = d ∧
      #(A + B) = k} = n + ∑ j ∈ Icc 1 (m - 1), min d (n - j) := by
  simp_rw [← affineDim_eq_finrank_span_sub, ← sumsetCardLowerBound_eq]
  exact minCardAdd_eq_sumsetCardLowerBound hd hm hmn hn
end SumOfSetsInSeveralDimensions
