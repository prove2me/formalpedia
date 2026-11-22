-- Prove2me | solution 1 for Paper.Hypergraph.tree_path_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:24.149926+00:00
-- url     : https://prove2.me/submissions/f7ce0d87-9b04-4be7-b745-7d11b2d65d6b

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution {V : Type*} {G : SimpleGraph V} (hG : G.IsTree)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) : p.length = G.dist u v := by
  obtain ⟨q, hq, hd⟩ := (hG.connected u v).exists_path_of_dist
  have heq := congrArg Subtype.val (hG.isAcyclic.path_unique ⟨p, hp⟩ ⟨q, hq⟩)
  change p = q at heq
  rw [heq]
  exact hd
end Paper.Hypergraph
