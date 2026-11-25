-- Prove2me | solution 1 for SimpleGraph.exists_isEulerian_of_forall_even_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:44:12.741515+00:00
-- url     : https://prove2.me/submissions/39563b57-7d64-4c69-8697-12bb7f18e938

module
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_Euler_Basic
public import Theorems.Thm_SimpleGraph_exists_isEulerian_or_longer_trail

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (hconn : G.Connected)
    (heven : ∀ v, Even (G.degree v)) : ∃ u, ∃ p : G.Walk u u, p.IsEulerian := by
  by_contra hno
  have key : ∀ k : ℕ, ∃ a b, ∃ q : G.Walk a b, q.IsTrail ∧ k ≤ q.length := by
    intro k
    induction k with
    | zero =>
      obtain ⟨v⟩ := hconn.nonempty
      exact ⟨v, v, nil, by simp, le_rfl⟩
    | succ k ih =>
      obtain ⟨a, b, q, hq, hk⟩ := ih
      rcases exists_isEulerian_or_longer_trail hconn heven q hq with h | ⟨a', b', q', hq', hlt⟩
      · exact absurd h hno
      · exact ⟨a', b', q', hq', by omega⟩
  obtain ⟨a, b, q, hq, hk⟩ := key (G.edgeFinset.card + 1)
  have := hq.length_le_card_edgeFinset
  omega
end SimpleGraph
