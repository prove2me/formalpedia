-- Prove2me | solution 1 for QuadraticFloor.sum_range_even_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:53:58.205832+00:00
-- url     : https://prove2.me/submissions/8f4f2354-d65b-4079-a0a9-1da68013306e

module
public import Definitions.Def_QuadraticFloor_Defs
public import Definitions.Def_QuadraticFloor_RootCount

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ r ∈ range (2 * m + 1), (if Even r then f r else 0) = ∑ j ∈ range (m + 1), f (2 * j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun j => f (2 * j)) (m + 1)]
    have h1 : ¬ Even (2 * m + 1) := by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one m
    simp only [h1, ite_false, add_zero, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, even_two_mul,
      ite_true]
end QuadraticFloor
