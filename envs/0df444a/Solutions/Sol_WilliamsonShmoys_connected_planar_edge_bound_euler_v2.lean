-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound_euler_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:25:11.26644+00:00
-- url     : https://prove2.me/submissions/1caca5f3-b0fe-43a7-9b68-b0546edc910e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_euler_characteristic
import Theorems.Thm_WilliamsonShmoys_planar_face_incidence_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨F, hEuler⟩ :=
    WilliamsonShmoys.connected_planar_euler_characteristic K hconn hdraw
  have hFaces :=
    WilliamsonShmoys.planar_face_incidence_bound K hconn hdraw hV F hEuler
  omega