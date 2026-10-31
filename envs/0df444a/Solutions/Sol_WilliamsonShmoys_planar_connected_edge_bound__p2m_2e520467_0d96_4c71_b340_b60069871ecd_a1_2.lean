-- Prove2me | solution 2 for WilliamsonShmoys.planar_connected_edge_bound__p2m_2e520467_0d96_4c71_b340_b60069871ecd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:13:25.59099+00:00
-- url     : https://prove2.me/submissions/677b96da-c7dd-425b-9326-274b707ee854

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_three_or_more_vertices_connected_core

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hconn : H.Connected) (hV : 3 <= Fintype.card V) : H.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices_connected_core H hH hconn hV
