-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connect_components__p2m_b17d3809_e307_4597_82b6_1d4f1ebd7e38_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T09:10:12.450652+00:00
-- url     : https://prove2.me/submissions/435367a6-fc64-4060-a0cc-a7ebf72df740
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_connected_extension__p2m_ae236b28_36d0_427c_b659_9ad0e6481b28_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧ Q.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      P.edgeSet.ncard ≤ Q.edgeSet.ncard := by
  obtain ⟨Q, hPQ, hConn, hQDraw⟩ :=
    WilliamsonShmoys.planar_drawing_has_connected_extension__p2m_ae236b28_36d0_427c_b659_9ad0e6481b28_a1
      P hDraw
  exact ⟨Q, hPQ, hConn, hQDraw,
    Set.ncard_mono (SimpleGraph.edgeSet_mono hPQ)⟩