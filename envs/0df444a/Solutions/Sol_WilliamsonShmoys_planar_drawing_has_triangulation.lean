-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_triangulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:37:16.389336+00:00
-- url     : https://prove2.me/submissions/dccb9d87-c786-4377-bb16-7e2466e537cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_for_triangulation
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count_for_triangulation

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V, H ≤ J ∧ HasPlanarDrawingOn J ∧
      3 * Fintype.card V = J.edgeSet.ncard + 6 := by
  obtain ⟨J, hHJ, hJ, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension_for_triangulation H hH
  refine ⟨J, hHJ, hJ, ?_⟩
  apply WilliamsonShmoys.maximal_drawing_edge_count_for_triangulation J hJ hcard
  intro K hJK hK
  exact hmax K (hHJ.trans hJK) hK