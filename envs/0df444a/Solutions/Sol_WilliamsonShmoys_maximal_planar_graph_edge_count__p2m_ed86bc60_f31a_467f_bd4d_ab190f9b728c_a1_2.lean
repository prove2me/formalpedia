-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_ed86bc60_f31a_467f_bd4d_ab190f9b728c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:24:11.83138+00:00
-- url     : https://prove2.me/submissions/0be03fc6-64ba-402c-b7d7-46882e6ae03a

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_maximal_edge_count_20261026

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V - 6 = L.edgeSet.ncard :=
  WilliamsonShmoys.planar_triangulation_extension_maximal_edge_count_20261026 L hDraw hMax hV
