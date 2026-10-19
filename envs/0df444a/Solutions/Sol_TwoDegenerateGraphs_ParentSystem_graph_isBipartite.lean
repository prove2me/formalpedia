-- Prove2me | solution 1 for TwoDegenerateGraphs.ParentSystem.graph_isBipartite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/2fdc62a0-c8d0-44aa-954b-e0f9a4aaf66c

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_ParentSystem_graph_adj_iff

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.ParentSystem
namespace TwoDegenerateGraphs.ParentSystem
theorem _root_.solution {V : Type*} (P : ParentSystem V) :
    P.graph.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => (⟨P.level v % 2, by omega⟩ : Fin 2)) ?_⟩
  intro v u hadj
  apply Fin.ne_of_val_ne
  change P.level v % 2 ≠ P.level u % 2
  rcases (P.graph_adj_iff v u).mp hadj with ⟨_, huv | huv⟩
  · have hlevel := P.parent_level huv
    omega
  · have hlevel := P.parent_level huv
    omega
end TwoDegenerateGraphs.ParentSystem
