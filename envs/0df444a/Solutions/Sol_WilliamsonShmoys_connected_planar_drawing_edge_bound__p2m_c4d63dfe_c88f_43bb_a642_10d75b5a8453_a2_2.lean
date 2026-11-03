-- Prove2me | solution 2 for WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_c4d63dfe_c88f_43bb_a642_10d75b5a8453_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:28:39.307208+00:00
-- url     : https://prove2.me/submissions/77512414-40d0-40a8-8919-1b419040197d

import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_bound
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawingOn_edge_bound K hK hcard