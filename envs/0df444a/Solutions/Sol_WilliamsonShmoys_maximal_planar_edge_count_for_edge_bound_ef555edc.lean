-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_ef555edc
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:32:12.037032+00:00
-- url     : https://prove2.me/submissions/ed5092b4-aa14-4d3e-98a9-49e4c53e0f3f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_certificate
import Theorems.Thm_WilliamsonShmoys_face_count_arithmetic

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V,
      H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_count_certificate H hV hH hMax
  exact WilliamsonShmoys.face_count_arithmetic (Fintype.card V) H.edgeSet.ncard f hEuler hFaces