-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_edge_count_euler_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:15:19.113233+00:00
-- url     : https://prove2.me/submissions/7c6b3d6d-86a0-47f6-b27e-81a085edcbfe

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_96423339_d6c7_499e_a706_076681b42078

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hMax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L = K)
    (hCard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hDrawL, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_96423339_d6c7_499e_a706_076681b42078 K hDraw hCard
  have hEq : L = K := hMax L hKL hDrawL
  simpa [hEq] using hCount