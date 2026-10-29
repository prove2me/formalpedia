-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_inequality_of_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:04:45.116992+00:00
-- url     : https://prove2.me/submissions/0854f888-2cd6-486f-bb20-c3751a708630

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarFaceCertificate
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_certificate_from_arcs

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * L.edgeSet.ncard := by
  obtain ⟨c⟩ :=
    WilliamsonShmoys.planar_drawing_face_certificate_from_arcs L hV hconn hdraw
  refine ⟨c.boundaries.length, c.euler, ?_⟩
  rw [← c.edge_incidence]
  exact c.faces_have_length