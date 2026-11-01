-- Prove2me | solution 2 for WilliamsonShmoys.crossing_free_drawing_edge_bound__p2m_85154c6b_7137_4d28_9cf8_ac3f60076d56_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:11:16.302372+00:00
-- url     : https://prove2.me/submissions/3d30f1ce-c8a0-4aef-96fc-303094f14e55

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_2343a1b4_cbe5_4a48_b836_711e4285cb1c_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound__p2m_2343a1b4_cbe5_4a48_b836_711e4285cb1c_a1 H hH hcard
