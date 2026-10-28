-- Prove2me | solution 1 for WilliamsonShmoys.exists_same_vertex_edge_maximal_planar_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:13:52.261627+00:00
-- url     : https://prove2.me/submissions/b3bc4bce-6224-487f-862f-7c0d2a5a3773

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem S181max {V : Type} [Fintype V] (Q : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : Q G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ Q H ∧ ∀ K : SimpleGraph V, H ≤ K → Q K → K = H := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ Q J}).Finite := Set.toFinite _
  obtain ⟨K, hK⟩ := Set.Finite.exists_maximal hfin ⟨G, le_rfl, hG⟩
  exact ⟨K, hK.prop.1, hK.prop.2, fun N hN hPN =>
    le_antisymm (hK.2 ⟨le_trans hK.prop.1 hN, hPN⟩ hN) hN⟩

theorem S185nc {V : Type} [Fintype V] {G H : SimpleGraph V} (h : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.2 h) (Set.toFinite _)

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ G : SimpleGraph V,
      H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G ∧
        ∀ K : SimpleGraph V, G ≤ K →
          WilliamsonShmoys.HasPlanarDrawingOn K → K = G := by
  exact S181max WilliamsonShmoys.HasPlanarDrawingOn H hH
