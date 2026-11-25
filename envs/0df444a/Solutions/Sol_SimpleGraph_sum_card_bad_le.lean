-- Prove2me | solution 1 for SimpleGraph.sum_card_bad_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:58:49.497833+00:00
-- url     : https://prove2.me/submissions/ed963c7e-8749-45c4-94a7-c28c03a49433

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
namespace SimpleGraph
theorem _root_.solution (t r m : ℕ) :
    ∑ τ : Fin t → V, #{S ∈ (univ : Finset V).powersetCard r |
        #{u | ∀ v ∈ S, G.Adj v u} < m ∧ ∀ i, ∀ v ∈ S, G.Adj (τ i) v} ≤
      (Fintype.card V).choose r * m ^ t := by
  calc ∑ τ : Fin t → V, #{S ∈ (univ : Finset V).powersetCard r |
        #{u | ∀ v ∈ S, G.Adj v u} < m ∧ ∀ i, ∀ v ∈ S, G.Adj (τ i) v}
      = ∑ S ∈ (univ : Finset V).powersetCard r, #{τ : Fin t → V |
          #{u | ∀ v ∈ S, G.Adj v u} < m ∧ ∀ i, ∀ v ∈ S, G.Adj (τ i) v} := by
        simp only [card_eq_sum_ones, sum_filter]
        exact sum_comm
    _ ≤ ∑ _S ∈ (univ : Finset V).powersetCard r, m ^ t := by
        refine sum_le_sum fun S _ => ?_
        by_cases hS : #{u | ∀ v ∈ S, G.Adj v u} < m
        · simp only [hS, true_and]
          calc #{τ : Fin t → V | ∀ i, ∀ v ∈ S, G.Adj (τ i) v}
              = #{u | ∀ v ∈ S, G.Adj v u} ^ t := by
                rw [← Fintype.card_piFinset_const]
                congr 1
                ext τ
                simp [Fintype.mem_piFinset, G.adj_comm]
            _ ≤ m ^ t := Nat.pow_le_pow_left hS.le t
        · simp [hS]
    _ = _ := by rw [sum_const, card_powersetCard, card_univ, smul_eq_mul]
end SimpleGraph
