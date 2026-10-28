-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_for_face_accounting_57972424
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T00:56:28.447518+00:00
-- url     : https://prove2.me/submissions/e184f033-aaa1-48c8-b9e3-a238b5f01fff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_certificate_repair4_917de119
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_euler_certificate_repair4_917de119

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨F, instF, boundaryLength, hFace, hIncidence, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_certificate_repair4_917de119
      G hDraw hConn hCard
  letI : Fintype F := instF
  exact WilliamsonShmoys.planar_edge_bound_from_euler_certificate_repair4_917de119
    G boundaryLength hFace hIncidence hEuler