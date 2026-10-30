-- Prove2me | solution 1 for WilliamsonShmoys.planar_component_bridge_extension__p2m_654d6b40_351a_4feb_9abd_94332c593474_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:20:50.169274+00:00
-- url     : https://prove2.me/submissions/54a47d97-b8b3-4c77-955d-634f49033663
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_extension_with_more_edges__p2m_afb0646a_1b1c_43fc_91b8_89461203ac52_a1
import Theorems.Thm_SimpleGraph_exists_adj_across_components_of_connected_supergraph__p2m_afb0646a_1b1c_43fc_91b8_89461203ac52_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) (hNotConnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧ G.edgeSet.ncard < H.edgeSet.ncard ∧
        (∃ u v, ¬ G.Reachable u v ∧ H.Adj u v) := by
  obtain ⟨H, hSub, hDrawH, hMore, hHConnected⟩ :=
    WilliamsonShmoys.planar_connected_extension_with_more_edges__p2m_afb0646a_1b1c_43fc_91b8_89461203ac52_a1
      G hDraw hCard hNotConnected
  obtain ⟨u, v, hUnreachable, hAdj⟩ :=
    SimpleGraph.exists_adj_across_components_of_connected_supergraph__p2m_afb0646a_1b1c_43fc_91b8_89461203ac52_a1
      G H hSub hHConnected hNotConnected
  exact ⟨H, hSub, hDrawH, hMore, ⟨u, v, hUnreachable, hAdj⟩⟩