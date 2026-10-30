-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawable_edge_bound_3daf7e3a
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:54:38.948312+00:00
-- url     : https://prove2.me/submissions/9f2ce602-46fc-4748-a46a-6225292b7fad

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_face_inequality

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hPconn : P.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    P.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaceDegree⟩ :=
    WilliamsonShmoys.connected_planar_euler_face_inequality
      P hPdraw hPconn hCard
  omega