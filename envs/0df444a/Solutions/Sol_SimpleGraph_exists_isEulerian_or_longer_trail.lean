-- Prove2me | solution 1 for SimpleGraph.exists_isEulerian_or_longer_trail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:39:07.76715+00:00
-- url     : https://prove2.me/submissions/e57720fb-b97e-4c93-8a2b-4a9005be805a

module
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_Euler_Basic
public import Theorems.Thm_SimpleGraph_exists_adj_not_mem_edges_of_not_even
public import Theorems.Thm_SimpleGraph_exists_mem_support_adj_not_mem_edges

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (hconn : G.Connected)
    (heven : ∀ v, Even (G.degree v)) {u v : V} (p : G.Walk u v) (hp : p.IsTrail) :
    (∃ w, ∃ q : G.Walk w w, q.IsEulerian) ∨
      ∃ a b, ∃ q : G.Walk a b, q.IsTrail ∧ p.length < q.length := by
  by_cases huv : u = v
  · subst huv
    by_cases he : p.IsEulerian
    · exact Or.inl ⟨u, p, he⟩
    right
    obtain ⟨x, hx, y, hxy, hnot⟩ := exists_mem_support_adj_not_mem_edges hconn hp he
    refine ⟨y, x, cons hxy.symm (p.rotate x hx).reverse, ?_, ?_⟩
    · rw [isTrail_cons]
      refine ⟨((isTrail_rotate hx).mpr hp).reverse, ?_⟩
      rw [edges_reverse, List.mem_reverse, (rotate_edges p x hx).mem_iff, Sym2.eq_swap]
      exact hnot
    · rw [length_cons, length_reverse, ← length_edges, ← length_edges,
        (rotate_edges p x hx).perm.length_eq]
      omega
  · right
    have hodd : ¬ Even (p.edges.countP fun e => v ∈ e) := by
      rw [hp.even_countP_edges_iff v]
      simp [huv]
    obtain ⟨y, hvy, hnot⟩ := exists_adj_not_mem_edges_of_not_even hp (heven v) hodd
    refine ⟨y, u, cons hvy.symm p.reverse, ?_, ?_⟩
    · rw [isTrail_cons]
      refine ⟨hp.reverse, ?_⟩
      rw [edges_reverse, List.mem_reverse, Sym2.eq_swap]
      exact hnot
    · simp
end SimpleGraph
