-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_triangulated_extension_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T16:43:46.95648+00:00
-- url     : https://prove2.me/submissions/8d239295-0172-44a5-9d74-bad8dc82b7ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_on_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_on_maximal_extension K hK hV
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_drawing_on_edge_count L hL hV hMax⟩