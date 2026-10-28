-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_bound_f12a69bf_0e8d_45a5_8cf0_59db52a03d9f
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:10:35.076554+00:00
-- url     : https://prove2.me/submissions/8436948d-100c-47b8-807f-2120b2b41d8a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_triangulation_extension_3daebd93
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hKdraw, hKcount⟩ :=
    WilliamsonShmoys.planar_drawing_edge_count_triangulation_extension_3daebd93 H hV hH
  have hKH : K = H := hmax K hHK hKdraw
  subst K
  exact le_of_eq hKcount