-- Prove2me | solution 1 for P2M_SumOfSetsInSeveralDimensions_le_two_mul_sub_one_of_isAddFreimanIso_of_finrank_span_sub_eq__2a5407090778
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:52.615224+00:00
-- url     : https://prove2.me/submissions/8e7f9262-ac4d-4ad4-8253-d72922406dcc

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_ClosedForm
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimensionSumsetBounds
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_MinCardAdd
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_Solution
public import Theorems.Thm_SumOfSetsInSeveralDimensions_le_two_mul_sub_one_of_isAddFreimanIso_of_finrank_span_sub_eq


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open SumOfSetsInSeveralDimensions
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {r : ℕ} {κ : ℝ} {X : Finset G} {f : G → Fin r → ℝ}
    (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin r → ℝ)) f)
    (hdim : Module.finrank ℝ (Submodule.span ℝ (↑(X.image f) - ↑(X.image f) : Set (Fin r → ℝ))) =
      r) :
    (r : ℝ) ≤ 2 * κ - 1 :=
  le_two_mul_sub_one_of_isAddFreimanIso_of_finrank_span_sub_eq hX hXX hf hdim
end SumOfSetsInSeveralDimensions
