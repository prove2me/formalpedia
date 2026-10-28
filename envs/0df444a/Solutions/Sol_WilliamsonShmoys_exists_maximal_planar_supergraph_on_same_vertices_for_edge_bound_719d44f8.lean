-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_on_same_vertices_for_edge_bound_719d44f8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:39:36.820898+00:00
-- url     : https://prove2.me/submissions/0e6cb180-ab0b-4297-98de-241d09db2c16

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

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
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, h1, h2, h3⟩ := S181max WilliamsonShmoys.HasPlanarDrawingOn G hG
  exact ⟨H, h1, h2, h3, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono h1) (Set.toFinite _)⟩
