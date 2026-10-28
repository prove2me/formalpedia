-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_bound_from_arcs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T13:35:25.865668+00:00
-- url     : https://prove2.me/submissions/d752f2c6-d338-4f18-9546-d2bca03ed29b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawing_euler_face_certificate

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨F, hEuler, hFace⟩ :=
    WilliamsonShmoys.drawing_euler_face_certificate K hconn hdraw hV
  omega