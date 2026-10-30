-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_d4833247_a107_430f_bfde_1b2cd697853a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:28:55.708677+00:00
-- url     : https://prove2.me/submissions/9050a36e-cd1e-4d02-9a17-984d087c8152
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_2f30e2d9_4845_4c04_a5c2_ea4608bfb1b9_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2f30e2d9_4845_4c04_a5c2_ea4608bfb1b9_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ T : SimpleGraph V,
      Set.Subset H.edgeSet T.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hHT, hT, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal__p2m_2f30e2d9_4845_4c04_a5c2_ea4608bfb1b9_a1 H hdraw
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_2f30e2d9_4845_4c04_a5c2_ea4608bfb1b9_a1 T hV hT hmax
  exact ⟨T, hHT, hT, hcount⟩