-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:12:11.842016+00:00
-- url     : https://prove2.me/submissions/0c95fd50-3528-408c-b8dd-28059198daef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_drawing_extension
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_on_finite_type

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K <= L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_planar_drawing_extension K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.edge_count_of_maximal_planar_drawing_on_finite_type
      L hV hL hmax⟩