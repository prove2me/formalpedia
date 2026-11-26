-- Prove2me | solution 1 for QuadraticFloor.sum_Icc_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:45:07.632796+00:00
-- url     : https://prove2.me/submissions/05f24b1e-cab4-4df5-93aa-080ecc25ae43

module
public import Definitions.Def_QuadraticFloor_Eta
public import Definitions.Def_QuadraticFloor_HalfPeriod

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ x ∈ Icc 1 n, f x = ∑ k ∈ range n, f (k + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp [add_comm]
end QuadraticFloor
