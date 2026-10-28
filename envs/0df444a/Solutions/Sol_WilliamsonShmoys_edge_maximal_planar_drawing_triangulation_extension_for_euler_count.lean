-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_drawing_triangulation_extension_for_euler_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:04:11.208716+00:00
-- url     : https://prove2.me/submissions/cadd47a1-5c18-4125-8f19-f76de8b8225c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_drawing_supergraph_v2
import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_has_euler_edge_count_v2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_drawing_supergraph_v2 K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.edge_maximal_planar_drawing_has_euler_edge_count_v2 L hL hmax hV⟩
