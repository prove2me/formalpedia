-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_1bec9fe1_f96d_4d95_8b96_08ac82faf267_a9
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:22:42.135032+00:00
-- url     : https://prove2.me/submissions/643648dd-0cf5-4ee9-85a4-214df7e48eed

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_retry2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hConn : M.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    (M.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 :=
  WilliamsonShmoys.planar_drawing_edge_upper_bound_retry2 M hV hDraw
