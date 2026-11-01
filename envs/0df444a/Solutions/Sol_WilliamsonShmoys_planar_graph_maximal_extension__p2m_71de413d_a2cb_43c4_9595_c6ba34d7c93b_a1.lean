-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_maximal_extension__p2m_71de413d_a2cb_43c4_9595_c6ba34d7c93b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:23:41.561079+00:00
-- url     : https://prove2.me/submissions/a3b37790-33a1-4d1a-b20a-d7693c8d0793

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_connectedification_retry3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 <= Fintype.card V) : ∃ H : SimpleGraph V, G ≤ H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H :=
  WilliamsonShmoys.planar_drawing_maximal_extension_connectedification_retry3 G hDraw
