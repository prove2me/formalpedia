-- Prove2me | solution 1 for SimpleGraph.sum_card_commonNeighbors_tuple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:58:41.404345+00:00
-- url     : https://prove2.me/submissions/c2dda99b-8e9b-4e68-b5dd-ef9c81788dff

module
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_DependentRandomChoice

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
omit [DecidableEq V]
namespace SimpleGraph
theorem _root_.solution (t : ℕ) :
    ∑ τ : Fin t → V, #{v | ∀ i, G.Adj (τ i) v} = ∑ v, G.degree v ^ t := by
  simp_rw [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [← card_filter, ← card_neighborFinset_eq_degree, ← Fintype.card_piFinset_const]
  congr 1
  ext τ
  simp [Fintype.mem_piFinset, G.adj_comm]
end SimpleGraph
