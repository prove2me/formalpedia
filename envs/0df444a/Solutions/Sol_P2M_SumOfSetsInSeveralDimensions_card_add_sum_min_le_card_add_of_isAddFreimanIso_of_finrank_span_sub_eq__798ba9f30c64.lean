-- Prove2me | solution 1 for P2M_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_isAddFreimanIso_of_finrank_span_sub_eq__798ba9f30c64
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:07.20143+00:00
-- url     : https://prove2.me/submissions/fd63c5a1-77a8-4a1d-a0a8-71c8daa51c9e

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_ClosedForm
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimensionSumsetBounds
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_MinCardAdd
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_Solution
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_add_sum_min_le_card_add_of_isAddFreimanIso_of_finrank_span_sub_eq


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open SumOfSetsInSeveralDimensions
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {G : Type*}
    [DecidableEq G] [AddCommMonoid G] {r : ℕ} {A B : Finset G} {f : G → Fin r → ℝ}
    (hB : B.Nonempty) (hBA : #B ≤ #A)
    (hf : IsAddFreimanIso 2 ((A ∪ B : Finset G) : Set G) ((A ∪ B).image f : Set (Fin r → ℝ)) f)
    (hdim : Module.finrank ℝ (Submodule.span ℝ
      (↑((A ∪ B).image f) - ↑((A ∪ B).image f) : Set (Fin r → ℝ))) = r) :
    #A + ∑ t ∈ Icc 1 (#B - 1), min (r - 1) (#A - t) ≤ #(A + B) :=
  card_add_sum_min_le_card_add_of_isAddFreimanIso_of_finrank_span_sub_eq hB hBA hf hdim
end SumOfSetsInSeveralDimensions
