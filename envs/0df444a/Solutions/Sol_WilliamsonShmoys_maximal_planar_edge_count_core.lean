-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_core
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:27:00.468498+00:00
-- url     : https://prove2.me/submissions/fda34e56-8e56-4a57-92f7-bd2382fcfd23

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_7369a359

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : forall J : SimpleGraph V, K <= J ->
      WilliamsonShmoys.HasPlanarDrawingOn J -> J = K)
    (hCard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition_7369a359 K hDraw hMax hCard
  omega