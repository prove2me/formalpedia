-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition_7369a359
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:51:02.956303+00:00
-- url     : https://prove2.me/submissions/64bf5662-f07f-494b-bb58-2542c7c048c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count_7369a359
import Theorems.Thm_WilliamsonShmoys_face_count_arithmetic_7369a359

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : forall J : SimpleGraph V, K <= J ->
      WilliamsonShmoys.HasPlanarDrawingOn J -> J = K)
    (hCard : 3 <= Fintype.card V) :
    exists f : Nat,
      Fintype.card V + f = K.edgeSet.ncard + 2 /\
      3 * f = 2 * K.edgeSet.ncard := by
  obtain ⟨H, hKH, hHDraw, hHEdges⟩ :=
    WilliamsonShmoys.maximal_planar_completion_edge_count_7369a359
      K hDraw hCard
  have hHK : H = K := hMax H hKH hHDraw
  have hKEdges : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    rw [← hHK]
    exact hHEdges
  exact WilliamsonShmoys.face_count_arithmetic_7369a359
    (Fintype.card V) K.edgeSet.ncard hCard hKEdges
