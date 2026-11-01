-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_between_unreachable__p2m_69b1ec23_7e07_4ae5_a2a3_1213925ce8f9_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:17:40.40019+00:00
-- url     : https://prove2.me/submissions/de0c29b9-1bd3-4840-8f1a-072d07f92b23
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
import Theorems.Thm_WilliamsonShmoys_planar_component_extension__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
import Theorems.Thm_WilliamsonShmoys_connected_extension_has_cross_edge__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hNotConnected : ¬ K.Connected) :
    ∃ u v : V, ¬ K.Reachable u v ∧
      ∃ H : SimpleGraph V,
        HasPlanarDrawingOn H ∧ K ≤ H ∧
        ∀ x y : V,
          H.Adj x y ↔
            K.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  obtain ⟨H, hH, hKH, hHConnected, hCross⟩ :=
    WilliamsonShmoys.planar_component_extension__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
      K hK hNotConnected
  obtain ⟨u, v, hUnreachable, hEdge⟩ :=
    WilliamsonShmoys.connected_extension_has_cross_edge__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
      K H hKH hHConnected hNotConnected hCross
  refine ⟨u, v, hUnreachable, ?_⟩
  exact WilliamsonShmoys.planar_drawing_subgraph__p2m_90606238_5f2e_48e5_b7d6_6d686b1c2a5f_a1
    K H hH hKH u v hUnreachable hEdge