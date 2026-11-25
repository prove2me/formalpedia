-- Prove2me | solution 1 for RegularSubgraph.four_regular_sup_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:34:23.257503+00:00
-- url     : https://prove2.me/submissions/2d862ccf-1d9a-431a-bb72-dfe14330ce23

module
public import Mathlib
public import Definitions.Def_RegularSubgraphLib_RegularSubgraph
public import Theorems.Thm_RegularSubgraph_exists_regular_subgraph

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph MvPolynomial Finset
open RegularSubgraph
variable {V : Type*} [Fintype V]
namespace RegularSubgraph
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsRegularOfDegree 4) {u w : V} (huw : u ≠ w) (hn : ¬ G.Adj u w) :
    ∃ H : SimpleGraph V, H ≤ G ⊔ edge u w ∧ H ≠ ⊥ ∧
      ∀ v, (H.neighborSet v).ncard = 0 ∨ (H.neighborSet v).ncard = 3 := by
  classical
  refine exists_regular_subgraph (G ⊔ edge u w) Nat.prime_three (fun v => ?_) ?_
  · -- degrees at most 5
    have hsub : (G ⊔ edge u w).neighborFinset v ⊆
        insert (if v = u then w else u) (G.neighborFinset v) := by
      intro x hx
      rw [mem_neighborFinset, sup_adj, edge_adj] at hx
      rw [Finset.mem_insert, mem_neighborFinset]
      rcases hx with hx | ⟨hx, hvx⟩
      · exact Or.inr hx
      · left
        rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp
        · simp [huw.symm]
    rw [← card_neighborFinset_eq_degree]
    refine (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans ?_)
    rw [card_neighborFinset_eq_degree, hG v]
  · -- 2 e(G ⊔ uw) = 4 n + 2
    have h1 : #(G ⊔ edge u w).edgeFinset = #G.edgeFinset + 1 := by
      convert G.card_edgeFinset_sup_edge hn huw
    have h2 : ∑ v, G.degree v = 2 * #G.edgeFinset := G.sum_degrees_eq_twice_card_edges
    simp only [hG.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h2
    have key : (2 * 3 - 2) * Fintype.card V < 2 * (#G.edgeFinset + 1) := by omega
    convert key using 3
    convert h1 using 2
    ext; simp
end RegularSubgraph
