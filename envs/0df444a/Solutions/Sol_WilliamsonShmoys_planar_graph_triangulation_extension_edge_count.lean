-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_triangulation_extension_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:20:07.279977+00:00
-- url     : https://prove2.me/submissions/74251955-7122-430a-809f-fc2dc527d0db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_d839d705_6fcc_4c88_b277_9f84682e1a8e
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_d839d705_6fcc_4c88_b277_9f84682e1a8e

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_d839d705_6fcc_4c88_b277_9f84682e1a8e H hV hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_edge_count_d839d705_6fcc_4c88_b277_9f84682e1a8e K hV hK hmax⟩