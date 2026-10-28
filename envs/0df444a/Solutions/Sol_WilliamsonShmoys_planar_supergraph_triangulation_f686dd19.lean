-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_f686dd19
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:54:20.452567+00:00
-- url     : https://prove2.me/submissions/af90725f-480d-461e-ad17-33870214c87f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_e696380b
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_e696380b

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph_e696380b G hV hG
  exact ⟨K, hGK, hK,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_e696380b K hV hK hmax⟩
