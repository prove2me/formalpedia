-- Prove2me | solution 1 for SimpleGraph.sq_two_mul_sub_le_card_mul_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:42:32.669058+00:00
-- url     : https://prove2.me/submissions/b3be4a74-f5ce-4088-a768-a74b4c569bb0

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Zify
public import Definitions.Def_GoodmanSupersaturation_Goodman

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable [Fintype V]
namespace SimpleGraph
theorem _root_.solution :
    (2 * ((#G.edgeFinset : ℤ) - #Gᶜ.edgeFinset)) ^ 2 ≤
      Fintype.card V * ∑ v, ((G.degree v : ℤ) - Gᶜ.degree v) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset V))
    (f := fun v => (G.degree v : ℤ) - Gᶜ.degree v)
  rw [card_univ] at h
  have hs : ∑ v, ((G.degree v : ℤ) - Gᶜ.degree v) =
      2 * ((#G.edgeFinset : ℤ) - #Gᶜ.edgeFinset) := by
    rw [sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges,
      Gᶜ.sum_degrees_eq_twice_card_edges]
    push_cast
    ring
  rw [← hs]
  exact h
end SimpleGraph
