-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_triangulated_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:18:50.53766+00:00
-- url     : https://prove2.me/submissions/af6006f7-ee2e-4174-a733-00dc0b766af7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension_for_triangulated_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_for_triangulated_extension

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H <= K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hHK, hDrawK, hMax⟩ :=
    WilliamsonShmoys.planar_drawingOn_maximal_extension_for_triangulated_extension
      H hDraw
  exact ⟨K, hHK, hDrawK,
    WilliamsonShmoys.maximal_planar_drawingOn_edge_count_for_triangulated_extension
      K hDrawK hCard hMax⟩
