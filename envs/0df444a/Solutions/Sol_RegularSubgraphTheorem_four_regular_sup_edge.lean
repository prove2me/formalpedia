-- Prove2me | solution 1 for RegularSubgraphTheorem.four_regular_sup_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:39:57.816531+00:00
-- url     : https://prove2.me/submissions/27994f23-52f1-4366-abbd-e8306269db7a

module
public import Mathlib
public import Definitions.Def_RegularSubgraphLib_RegularSubgraph
public import Definitions.Def_RegularSubgraphs_Solution
public import Theorems.Thm_RegularSubgraph_four_regular_sup_edge


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open RegularSubgraphTheorem
variable {V : Type*} [Fintype V]
namespace RegularSubgraphTheorem
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsRegularOfDegree 4) {u w : V} (huw : u ≠ w) (hn : ¬ G.Adj u w) :
    ∃ H : SimpleGraph V, H ≤ G ⊔ edge u w ∧ H ≠ ⊥ ∧
      ∀ v, (H.neighborSet v).ncard = 0 ∨ (H.neighborSet v).ncard = 3 :=
  RegularSubgraph.four_regular_sup_edge G hG huw hn
end RegularSubgraphTheorem
