-- Prove2me | solution 2 for WilliamsonShmoys.planar_graph_edge_upper_bound__p2m_648e2563_4933_48d5_af68_a43e4e82ab0d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:25:19.158588+00:00
-- url     : https://prove2.me/submissions/cc866d6e-3586-4895-b3e7-66abcbc93411

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound K hK hV
