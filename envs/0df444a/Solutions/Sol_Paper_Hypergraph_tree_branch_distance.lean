-- Prove2me | solution 1 for Paper.Hypergraph.tree_branch_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:12.302953+00:00
-- url     : https://prove2.me/submissions/96b55715-60ec-4acc-92a7-b6f65156954b

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_tree_path_length

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    {t r u : V} (htr : G.Adj t r) (hu : u ≠ t)
    (hr : (G.induce {v | v ≠ t}).Reachable ⟨r, htr.ne.symm⟩ ⟨u, hu⟩) :
    G.dist t u = G.dist r u + 1 := by
  classical
  obtain ⟨p, hp, _⟩ := hr.exists_path_of_dist
  let q : G.Walk r u := p.map (SimpleGraph.Embedding.induce {v | v ≠ t}).toHom
  have hq : q.IsPath := SimpleGraph.Walk.map_isPath_of_injective (by intro a b h; exact Subtype.ext h) hp
  have ht : t ∉ q.support := by
    have hs : q.support = p.support.map (fun v => v.val) := SimpleGraph.Walk.support_map _ _
    rw [hs]
    simp only [List.mem_map]
    rintro ⟨v, _, hv⟩
    exact v.property hv
  have hc : (SimpleGraph.Walk.cons htr q).IsPath := by
    exact (SimpleGraph.Walk.cons_isPath_iff htr q).mpr ⟨hq, ht⟩
  rw [← tree_path_length hG hc, ← tree_path_length hG hq]
  simp
end Paper.Hypergraph
