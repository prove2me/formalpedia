-- Prove2me | solution 1 for SimpleGraph.sum_card_commonNeighbors_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:14.037303+00:00
-- url     : https://prove2.me/submissions/6e9b0585-ce51-4f31-9a96-eef6ea590404

module
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Definitions.Def_RamseyReservoir_Book
public import Theorems.Thm_SimpleGraph_sum_card_commonNeighbors_eq_card_orderedTriangles
public import Theorems.Thm_SimpleGraph_card_orderedTriangles

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution [DecidableEq V] :
    ∑ u, ∑ v ∈ G.neighborFinset u, Fintype.card (G.commonNeighbors u v) =
      6 * #(G.cliqueFinset 3) := by
  rw [sum_card_commonNeighbors_eq_card_orderedTriangles, card_orderedTriangles]
end SimpleGraph
