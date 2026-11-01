-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulated_supergraph_edge_lower_bound__p2m_0ac110bd_aaad_4255_8185_0d10e2119357_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:45:51.187732+00:00
-- url     : https://prove2.me/submissions/5acba7a2-9ca4-4944-b40a-1f9943481fa0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_150f7ba2_65b7_4a49_8255_d3333730e062_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_150f7ba2_65b7_4a49_8255_d3333730e062_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_150f7ba2_65b7_4a49_8255_d3333730e062_a1
      H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_150f7ba2_65b7_4a49_8255_d3333730e062_a1
      K hcard hK hmax⟩