-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_extends_to_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:08:13.460537+00:00
-- url     : https://prove2.me/submissions/35d61432-7195-4451-a8f2-79cbef91c259
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_maximal
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_formula

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧ WilliamsonShmoys.HasPlanarDrawingOn R ∧
        R.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨R, hQR, hRdraw, hRmax⟩ :=
    WilliamsonShmoys.planar_augmentation_maximal (V := V) Q hV hQdraw
  exact ⟨R, hQR, hRdraw,
    WilliamsonShmoys.maximal_planar_graph_edge_formula R hV hRdraw hRmax⟩