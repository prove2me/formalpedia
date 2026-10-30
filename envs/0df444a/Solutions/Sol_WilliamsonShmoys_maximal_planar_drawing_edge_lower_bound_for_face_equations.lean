-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound_for_face_equations
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:41:35.307723+00:00
-- url     : https://prove2.me/submissions/7152ac61-f1c8-407a-827e-ab50db94e793

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_count_certificate
import Mathlib.Tactic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  apply Exists.elim
    (WilliamsonShmoys.maximal_planar_drawing_face_count_certificate L hL hMax hCard)
  intro f hf
  omega