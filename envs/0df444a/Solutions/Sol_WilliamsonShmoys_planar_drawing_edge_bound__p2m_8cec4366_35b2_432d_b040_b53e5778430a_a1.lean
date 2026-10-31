-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound__p2m_8cec4366_35b2_432d_b040_b53e5778430a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:27:58.172566+00:00
-- url     : https://prove2.me/submissions/1ba10443-5a80-462d-9aef-7da284d7e105

import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_v3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hconn : T.Connected) : T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.connected_planar_edge_bound_v3 T hV hT hconn
