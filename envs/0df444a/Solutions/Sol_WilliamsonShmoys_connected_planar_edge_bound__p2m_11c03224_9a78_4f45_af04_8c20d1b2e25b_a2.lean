-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_11c03224_9a78_4f45_af04_8c20d1b2e25b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:50:31.630996+00:00
-- url     : https://prove2.me/submissions/3ad61858-40af-491f-9ac3-1869f229b625

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_three_or_more_vertices_connected_core

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {W : Type} [Fintype W] [LinearOrder W]
    (G : SimpleGraph W) (hG : HasPlanarDrawingOn G)
    (hconn : G.Connected) (hcard : 3 <= Fintype.card W) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card W :=
  WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices_connected_core G hG hconn hcard
