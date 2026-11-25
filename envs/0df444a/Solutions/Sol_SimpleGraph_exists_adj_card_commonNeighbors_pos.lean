-- Prove2me | solution 1 for SimpleGraph.exists_adj_card_commonNeighbors_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:35:23.033841+00:00
-- url     : https://prove2.me/submissions/28c3521a-a8a3-4e82-8198-e1d00a21967d

module
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Definitions.Def_RamseyReservoir_Book
public import Theorems.Thm_SimpleGraph_exists_adj_four_mul_card_edgeFinset_le

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution (h : Fintype.card V ^ 2 < 4 * #G.edgeFinset) :
    ∃ u v, G.Adj u v ∧ 0 < Fintype.card (G.commonNeighbors u v) := by
  have hE : G.edgeFinset.Nonempty := card_pos.mp (by omega)
  obtain ⟨u, v, huv, h'⟩ := exists_adj_four_mul_card_edgeFinset_le hE
  refine ⟨u, v, huv, Nat.pos_of_ne_zero fun h0 => ?_⟩
  rw [h0, zero_add, ← sq] at h'
  omega
end SimpleGraph
