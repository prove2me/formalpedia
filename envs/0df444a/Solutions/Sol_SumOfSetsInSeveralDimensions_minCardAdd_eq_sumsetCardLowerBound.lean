-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.minCardAdd_eq_sumsetCardLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:48.514372+00:00
-- url     : https://prove2.me/submissions/6a60e3d5-458e-4e22-87b9-238daae3a1d5

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
public import Theorems.Thm_Finset_affineDim_add_eq_of_left_eq
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add
public import Theorems.Thm_SumOfSetsInSeveralDimensions_exists_card_add_eq_sumsetCardLowerBound
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sumsetCardLowerBound_eq

section
@[expose] public section
namespace SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {d m n : ℕ}
private lemma sumsetCardLowerBound_le_card_add {A B : Finset (Fin d → ℝ)} (hm : 1 ≤ m)
    (hmn : m ≤ n) (hA : #A = m) (hB : #B = n) (hdim : (A + B).affineDim = d) :
    sumsetCardLowerBound d m n ≤ #(A + B) := by
  have h := card_add_sum_min_le_card_add (d := d) (A := B) (B := A) (card_pos.1 (by grind))
    (by grind) (by rwa [add_comm])
  rwa [add_comm B, hA, hB, ← sumsetCardLowerBound_eq] at h
end SumOfSetsInSeveralDimensions
end
end

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
variable {d m n : ℕ}
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution (hd : 1 ≤ d) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hn : d + 1 ≤ n) : minCardAdd d m n = sumsetCardLowerBound d m n := by
  obtain ⟨A, B, hA, hB, hBdim, hAB⟩ := exists_card_add_eq_sumsetCardLowerBound hd hm hmn hn
  have hdim : (A + B).affineDim = d := by
    rw [add_comm]
    exact affineDim_add_eq_of_left_eq (card_pos.1 (by grind)) hBdim
  refine le_antisymm (Nat.sInf_le ⟨A, B, hA, hB, hdim, hAB⟩)
    (le_csInf ⟨_, A, B, hA, hB, hdim, rfl⟩ ?_)
  rintro k ⟨A', B', hA', hB', hdim', rfl⟩
  exact sumsetCardLowerBound_le_card_add hm hmn hA' hB' hdim'
end SumOfSetsInSeveralDimensions
