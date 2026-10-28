-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_certificate_from_arcs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:23:07.304522+00:00
-- url     : https://prove2.me/submissions/ea791f6e-5d50-401e-96ff-ebd0b1cca506
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarFaceCertificate
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bounds_41afc169_9eb4_4682_8d03_09ec36ef1b9a
import Theorems.Thm_WilliamsonShmoys_face_certificate_from_edge_bounds_41afc169_9eb4_4682_8d03_09ec36ef1b9a

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Nonempty (WilliamsonShmoys.PlanarFaceCertificate L) := by
  obtain ⟨hmin, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_edge_bounds_41afc169_9eb4_4682_8d03_09ec36ef1b9a L hV hconn hdraw
  exact WilliamsonShmoys.face_certificate_from_edge_bounds_41afc169_9eb4_4682_8d03_09ec36ef1b9a L hV hmin hmax