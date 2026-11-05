-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_from_local_addition__p2m_69b1ec23_7e07_4ae5_a2a3_1213925ce8f9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:11:54.066209+00:00
-- url     : https://prove2.me/submissions/fd97049e-2fc9-4080-a984-8838f170611f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_local_extension_connected__p2m_92ab9f16_2d15_4356_b6df_90082235199d_a1
import Mathlib
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hstep : ∀ (G : SimpleGraph V), HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ u v : V, ¬ G.Reachable u v ∧
        ∃ H : SimpleGraph V,
          HasPlanarDrawingOn H ∧ G ≤ H ∧
          ∀ x y : V,
            H.Adj x y ↔
              G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧ H.Connected ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact WilliamsonShmoys.finite_graph_local_extension_connected__p2m_92ab9f16_2d15_4356_b6df_90082235199d_a1
    (P := HasPlanarDrawingOn) K hK hstep