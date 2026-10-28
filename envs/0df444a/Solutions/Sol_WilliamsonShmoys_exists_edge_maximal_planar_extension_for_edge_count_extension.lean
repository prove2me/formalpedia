-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_maximal_planar_extension_for_edge_count_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:45.434017+00:00
-- url     : https://prove2.me/submissions/6ee62ed4-3fb5-4e80-a50a-bd8ed2961b84

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
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ J : SimpleGraph V,
      HasPlanarDrawingOn J ∧ G.edgeSet ⊆ J.edgeSet ∧
        ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
          J.edgeSet ⊆ K.edgeSet → K.edgeSet ⊆ J.edgeSet := by
  obtain ⟨J, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn G hG
  exact ⟨J, h2, SimpleGraph.edgeSet_mono h1, fun K hK hJK => by
    rw [h3 K (SimpleGraph.edgeSet_subset_edgeSet.1 hJK) hK]⟩
