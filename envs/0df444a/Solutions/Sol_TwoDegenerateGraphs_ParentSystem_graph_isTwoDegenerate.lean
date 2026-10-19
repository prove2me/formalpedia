-- Prove2me | solution 1 for TwoDegenerateGraphs.ParentSystem.graph_isTwoDegenerate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/4a86ac28-8f8b-4902-8703-17c0f7995269

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
    IsTwoDegenerate P.graph := by
  classical
  intro s hs
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image s P.level hs
  refine ⟨v, hv, ?_⟩
  have hsubset : neighborsWithin P.graph s v ⊆ P.parents v := by
    intro u hu
    have hus : u ∈ s ∧ P.graph.Adj v u := by
      simpa [neighborsWithin] using hu
    rcases (P.graph_adj_iff v u).mp hus.2 with ⟨_, hparent | hchild⟩
    · exact hparent
    · have hlevel := P.parent_level hchild
      have hle := hmax u hus.1
      omega
  exact (Finset.card_le_card hsubset).trans (P.parent_card v)
end TwoDegenerateGraphs.ParentSystem
