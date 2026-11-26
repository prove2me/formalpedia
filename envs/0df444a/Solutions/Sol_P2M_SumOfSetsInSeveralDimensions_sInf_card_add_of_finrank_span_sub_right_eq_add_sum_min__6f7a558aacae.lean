-- Prove2me | solution 1 for P2M_SumOfSetsInSeveralDimensions_sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min__6f7a558aacae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:06.597575+00:00
-- url     : https://prove2.me/submissions/18103899-ba93-4335-b72a-5551ade51385

module
public import Definitions.Def_SumOfSetsInSeveralDimensions_ClosedForm
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimensionSumsetBounds
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_MinCardAdd
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SumOfSetsInSeveralDimensions_Solution
public import Theorems.Thm_SumOfSetsInSeveralDimensions_sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open SumOfSetsInSeveralDimensions
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {d m n : ℕ} (hd : 1 ≤ d)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hn : d + 1 ≤ n) :
    sInf {k | ∃ A B : Finset (Fin d → ℝ), #A = m ∧ #B = n ∧
      Module.finrank ℝ (Submodule.span ℝ (↑B - ↑B : Set (Fin d → ℝ))) = d ∧ #(A + B) = k} =
      n + ∑ j ∈ Icc 1 (m - 1), min d (n - j) :=
  sInf_card_add_of_finrank_span_sub_right_eq_add_sum_min hd hm hmn hn
end SumOfSetsInSeveralDimensions
