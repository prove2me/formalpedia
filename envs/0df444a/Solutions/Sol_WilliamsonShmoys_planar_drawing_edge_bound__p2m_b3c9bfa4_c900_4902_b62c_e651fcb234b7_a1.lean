-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_b3c9bfa4_c900_4902_b62c_e651fcb234b7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:11:16.180823+00:00
-- url     : https://prove2.me/submissions/c43d1a2a-c0dd-4490-86c9-89f32fe7cd5a

import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.simple_planar_edge_bound__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1 G hG hconn hcard
