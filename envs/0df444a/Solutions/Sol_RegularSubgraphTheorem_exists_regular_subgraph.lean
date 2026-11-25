-- Prove2me | solution 1 for RegularSubgraphTheorem.exists_regular_subgraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:37:06.836319+00:00
-- url     : https://prove2.me/submissions/6138db6c-8c54-4041-aa2a-cf6b0c329dc4

module
public import Mathlib
public import Definitions.Def_RegularSubgraphLib_RegularSubgraph
public import Definitions.Def_RegularSubgraphs_Solution
public import Theorems.Thm_RegularSubgraph_exists_regular_subgraph


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open RegularSubgraphTheorem
variable {V : Type*} [Fintype V]
namespace RegularSubgraphTheorem
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℕ} (hp : p.Prime)
    (hmax : ∀ v, G.degree v ≤ 2 * p - 1)
    (havg : (2 * p - 2) * Fintype.card V < 2 * #G.edgeFinset) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H ≠ ⊥ ∧
      ∀ v, (H.neighborSet v).ncard = 0 ∨ (H.neighborSet v).ncard = p :=
  RegularSubgraph.exists_regular_subgraph G hp hmax havg
end RegularSubgraphTheorem
