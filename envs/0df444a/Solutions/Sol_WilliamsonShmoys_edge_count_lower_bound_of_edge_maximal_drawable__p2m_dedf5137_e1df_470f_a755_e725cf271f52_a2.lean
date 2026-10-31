-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_lower_bound_of_edge_maximal_drawable__p2m_dedf5137_e1df_470f_a755_e725cf271f52_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:57:53.905089+00:00
-- url     : https://prove2.me/submissions/3b06ebe5-ffbb-436c-a67d-0a8c37e4e25e

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_20261026

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) (hMax : ∀ L : SimpleGraph V, G ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = G) : 3 * Fintype.card V - 6 ≤ G.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_edge_count_lower_bound_20261026 G hDraw hV hMax
