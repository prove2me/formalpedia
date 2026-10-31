-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_simple_edge_bound__p2m_2e66439f_db58_4f2d_a077_9b6daccbd657_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T20:59:40.341451+00:00
-- url     : https://prove2.me/submissions/81330aa9-a4cb-484d-ad32-f16a52122b83

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_three_or_more_vertices_connected_core

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) (hConnected : G.Connected) (hCard : 3 <= Fintype.card V) : G.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices_connected_core G hDraw hConnected hCard
