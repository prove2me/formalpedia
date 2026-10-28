-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_96423339_d6c7_499e_a706_076681b42078
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:39:36.485498+00:00
-- url     : https://prove2.me/submissions/3e6d2c42-94c4-41ec-a975-86bbe12a4f8d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_96423339_d6c7_499e_a706_076681b42078
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_96423339_d6c7_499e_a706_076681b42078

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ HasPlanarDrawingOn L ∧
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hDrawL, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_96423339_d6c7_499e_a706_076681b42078 K hDraw hCard
  have hCount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_96423339_d6c7_499e_a706_076681b42078 L hDrawL hCard hMax
  exact ⟨L, hKL, hDrawL, hCount⟩