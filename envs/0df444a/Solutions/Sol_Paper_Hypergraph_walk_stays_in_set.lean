-- Prove2me | solution 1 for Paper.Hypergraph.walk_stays_in_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:31.223845+00:00
-- url     : https://prove2.me/submissions/3e00d098-f69a-4d99-9a84-1068d0d8fea2

import Definitions.Def_Paper_RoundingCutoff
import Definitions.Def_Paper_RoundingRecursion
import Theorems.Thm_Paper_Hypergraph_walk_vertices


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (P : Finset ℕ)
    (hclosed : ∀ u ∈ P, ∀ v ∈ H.vertices, H.primal.Adj u v → v ∈ P)
    {u v : ℕ} (hu : u ∈ H.vertices) (huP : u ∈ P) (p : H.primal.Walk u v) : v ∈ P := by
  induction p with
  | nil => exact huP
  | @cons u w v huw p ih =>
    have hw := H.walk_vertices (.cons huw p) hu w (by simp)
    exact ih hw (hclosed u huP w hw huw)
end Paper.Hypergraph
