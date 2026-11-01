-- Prove2me | solution 2 for WilliamsonShmoys.simple_planar_edge_bound__p2m_09878566_3989_4e48_bc10_98e236546b3d_a1__p2m_09878566_3989_4e48_bc10_98e236546b3d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:12:14.281144+00:00
-- url     : https://prove2.me/submissions/cedd38c8-1cfa-4df1-8384-45fe47776b7f

import Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.simple_planar_edge_bound__p2m_34407b99_d8c1_41e6_9706_2994099c89a5_a1 G hG hconn hcard
