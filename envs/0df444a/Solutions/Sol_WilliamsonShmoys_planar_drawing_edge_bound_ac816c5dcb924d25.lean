-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_ac816c5dcb924d25
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:13:43.963982+00:00
-- url     : https://prove2.me/submissions/76cc2160-1b9e-4842-9995-fd4c155a07c3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_inequality_ac816c5dcb924d25
import Theorems.Thm_WilliamsonShmoys_face_inequality_edge_bound_ac816c5dcb924d25
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_face_inequality_ac816c5dcb924d25 H hV hconn hH
  exact WilliamsonShmoys.face_inequality_edge_bound_ac816c5dcb924d25
    H f hEuler hFaces