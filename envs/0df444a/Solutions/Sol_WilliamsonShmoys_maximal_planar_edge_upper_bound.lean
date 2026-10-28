-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T01:06:32.233127+00:00
-- url     : https://prove2.me/submissions/e8d69773-1a0d-4649-81a4-f069cb4bea98
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_certificate
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_euler_face_certificate

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, f, hHK, hEuler, hFaces⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_certificate H hV hDraw
  exact WilliamsonShmoys.edge_bound_of_euler_face_certificate
    H K hHK hV f hEuler hFaces