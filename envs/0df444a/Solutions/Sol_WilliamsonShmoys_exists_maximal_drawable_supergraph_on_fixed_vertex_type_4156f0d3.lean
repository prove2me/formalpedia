-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_drawable_supergraph_on_fixed_vertex_type_4156f0d3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:56:41.118803+00:00
-- url     : https://prove2.me/submissions/70bbcf0d-8fd7-4241-b084-4977a3e007cd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      Set.Subset G.edgeSet H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, Set.Subset H.edgeSet K.edgeSet →
        HasPlanarDrawingOn K → Set.Subset K.edgeSet H.edgeSet) := by
  obtain ⟨M, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn G hG
  refine ⟨M, SimpleGraph.edgeSet_subset_edgeSet.2 h1, h2, fun N hN hNp => ?_⟩
  have := h3 N (SimpleGraph.edgeSet_subset_edgeSet.1 hN) hNp
  subst this
  exact fun _ h => h
