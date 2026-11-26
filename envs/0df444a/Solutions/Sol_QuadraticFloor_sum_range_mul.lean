-- Prove2me | solution 1 for QuadraticFloor.sum_range_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:59.069928+00:00
-- url     : https://prove2.me/submissions/9f6c4723-0f3d-4564-a0cb-4fda723dbd48

module
public import Definitions.Def_QuadraticFloor_Eta
public import Definitions.Def_QuadraticFloor_HalfPeriod

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {M : Type*} [AddCommMonoid M] (F : ℕ → M) (m n : ℕ) :
    ∑ x ∈ range (m * n), F x = ∑ k ∈ range n, ∑ y ∈ range m, F (m * k + y) := by
  induction n with
  | zero => simp
  | succ n ih => rw [mul_add, mul_one, sum_range_add, ih, sum_range_succ]
end QuadraticFloor
