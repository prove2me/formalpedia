-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_edge_bound__p2m_996f417d_299f_4de3_98ff_54d66e679a8a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:23:39.892995+00:00
-- url     : https://prove2.me/submissions/310b7ce0-a462-41d9-98c0-d1ade1ffaf3d

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1 G hG hV
