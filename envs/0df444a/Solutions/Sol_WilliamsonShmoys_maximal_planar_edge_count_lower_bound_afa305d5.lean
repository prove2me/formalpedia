-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_afa305d5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:33:34.273107+00:00
-- url     : https://prove2.me/submissions/c79807b9-1746-424c-9a80-95bcab2f8a8b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_afa305d5
import Theorems.Thm_WilliamsonShmoys_euler_face_count_arithmetic_afa305d5

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall J : SimpleGraph V, H <= J ->
      WilliamsonShmoys.HasPlanarDrawingOn J -> J = H) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by
  obtain ⟨f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_face_count_afa305d5 H hDraw hCard hMax
  exact WilliamsonShmoys.euler_face_count_arithmetic_afa305d5
    (Fintype.card V) H.edgeSet.ncard f hEuler hIncidence